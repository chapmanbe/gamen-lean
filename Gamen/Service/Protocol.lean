import Lean.Data.Json

/-!
# Gamen.Service.Protocol

Port of `gamen-hs/protocol/Service/Protocol.hs`: the `dcleg-service`
request envelope and the `ok`/`error` response objects
(`notes/dcleg-service-protocol.md` §2, §6 in gamen-hs).

The Haskell gets three things from aeson that Lean's `Json` library does
differently, so this module supplies them, to keep responses byte-identical:

* **Encoding** (`encode`). aeson writes object keys in ascending order (as
  `Json.compress` does), but formats numbers as `Data.Scientific` does
  (`1.0e-2`, not `0.01`) and escapes `\b`/`\f` as `\u0008`/`\u000c`.
  Numbers reach a response only when `build` echoes a rejected
  `premises` value back as `details.received`.
* **Decoding messages** (`expected`, `parseList`, `parsePair`, …). Where
  the Haskell reports an aeson `fromJSON` failure (`formula_invalid`, and
  `model_invalid`'s `"JSON parse error: …"`), the message text is aeson's.
  These helpers reproduce the messages of the instances the service uses.
* **`Int` fields** (`parseInt`): aeson accepts any integral number in the
  64-bit range (`1.0`, `1e2`) and rejects the rest with the value printed
  by `Data.Scientific`'s `show`.

Malformed JSON text is the one case left to Lean's own parser message: the
code (`parse_error`) and envelope match, the advisory message does not
(aeson's text depends on its parser internals). Lean's parser also keeps
the *last* of two duplicate keys where aeson keeps the first.
-/

namespace Gamen.Service
open Lean (Json JsonNumber)

/-! ## Numbers as `Data.Scientific` prints them -/

/-- Decimal digits of `n` with trailing zeros removed, and the exponent `e`
with `n = 0.d₁d₂… × 10^e`; `([0], 0)` for zero. Haskell's
`toDecimalDigits`, for the value `n × 10^(-places)`. -/
def toDecimalDigits (n : Nat) (places : Nat) : List Char × Int :=
  if n == 0 then (['0'], 0) else
  let ds := (toString n).toList
  let e : Int := ds.length - places
  (ds.reverse.dropWhile (· == '0') |>.reverse, e)

/-- `Data.Scientific.formatScientific Generic Nothing`, which is also its
`show`: exponent form outside `0.1 ≤ |x| < 10^7`, fixed form inside. -/
def formatScientificGeneric (n : JsonNumber) : String :=
  let sign := if n.mantissa < 0 then "-" else ""
  let (ds, e) := toDecimalDigits n.mantissa.natAbs n.exponent
  let body :=
    if e < 0 || e > 7 then
      match ds with
      | ['0'] => "0.0e0"
      | [d] => String.ofList [d] ++ ".0e" ++ toString (e - 1)
      | d :: rest => String.ofList (d :: '.' :: rest) ++ "e" ++ toString (e - 1)
      | [] => "0.0e0"
    else if e ≤ 0 then
      "0." ++ String.ofList (List.replicate (-e).toNat '0') ++ String.ofList ds
    else
      let k := e.toNat
      let intPart := (ds.take k) ++ List.replicate (k - ds.length) '0'
      let frac := ds.drop k
      String.ofList intPart ++ "." ++ (if frac.isEmpty then "0" else String.ofList frac)
  sign ++ body

/-- aeson's number encoding: `formatScientificGeneric` when the decimal
exponent is negative or above 1024, otherwise the integer. Lean's parser
folds a positive exponent into the mantissa, so here "exponent above 1024"
means "more than 1024 trailing zeros": right for `1e1025`, wrong for a
literal written out with that many zeros (aeson prints it as an integer). -/
def encodeNumber (n : JsonNumber) : String :=
  if n.exponent != 0 then formatScientificGeneric n else
  let ds := (toString n.mantissa.natAbs).toList
  if n.mantissa != 0 && (ds.reverse.takeWhile (· == '0')).length > 1024 then
    formatScientificGeneric n
  else toString n.mantissa

/-! ## Encoding -/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- aeson's string escaping: `"`, `\`, `\n`, `\r`, `\t` by name, every other
control character below U+0020 as `\u00xx` (lowercase hex); everything else,
including U+007F and non-ASCII, verbatim. -/
def escapeString (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\""
    else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n"
    else if c == '\r' then "\\r"
    else if c == '\t' then "\\t"
    else if c.toNat < 0x20 then
      "\\u00" ++ String.ofList [hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
    else String.ofList [c]) ++ "\""

mutual
/-- A JSON value as aeson's `encode` writes it: compact, keys ascending.
Structural recursion through `Json`'s nested containers (the object map's
internal tree), so no fuel and no `partial` are needed. -/
def encode : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => encodeNumber n
  | .str s => escapeString s
  | .arr ⟨xs⟩ => "[" ++ encodeList xs ++ "]"
  | .obj ⟨⟨t⟩⟩ => "{" ++ ",".intercalate (encodeFields t) ++ "}"
/-- The elements of an array, comma-separated. -/
def encodeList : List Json → String
  | [] => ""
  | [x] => encode x
  | x :: xs => encode x ++ "," ++ encodeList xs
/-- `"key":value` for each field, in key order (in-order traversal). -/
def encodeFields : Std.DTreeMap.Internal.Impl String (fun _ => Json) → List String
  | .leaf => []
  | .inner _ k v l r => encodeFields l ++ [escapeString k ++ ":" ++ encode v] ++ encodeFields r
end

mutual
/-- Nesting depth of a JSON value (scalars 0). Gives the formula decoder
its fuel (`Gamen.Service.Formula`). -/
def depth : Json → Nat
  | .arr ⟨xs⟩ => depthList xs + 1
  | .obj ⟨⟨t⟩⟩ => depthFields t + 1
  | _ => 0
def depthList : List Json → Nat
  | [] => 0
  | x :: xs => max (depth x) (depthList xs)
def depthFields : Std.DTreeMap.Internal.Impl String (fun _ => Json) → Nat
  | .leaf => 0
  | .inner _ _ v l r => max (depth v) (max (depthFields l) (depthFields r))
end

/-! ## aeson-style decoding -/

/-- aeson's name for a value's JSON type, as in its `typeMismatch` messages. -/
def typeName : Json → String
  | .null => "Null"
  | .bool _ => "Boolean"
  | .num _ => "Number"
  | .str _ => "String"
  | .arr _ => "Array"
  | .obj _ => "Object"

/-- `expected X, but encountered Y`. -/
def expected (what : String) (j : Json) : String :=
  s!"expected {what}, but encountered {typeName j}"

/-- aeson's `withObject name`: the failure is
`parsing <name> failed, expected Object, but encountered …`. -/
def withObject {α : Type} (name : String) (j : Json) (k : Json → Except String α) :
    Except String α :=
  match j with
  | .obj _ => k j
  | _ => throw s!"parsing {name} failed, {expected "Object" j}"

/-- aeson's `.:` on an object: a missing key fails with `key "k" not found`;
a present key (`null` included) goes to the field parser. -/
def reqField {α : Type} (o : Json) (k : String) (p : Json → Except String α) :
    Except String α :=
  match o.getObjVal? k with
  | .ok v => p v
  | .error _ => throw s!"key \"{k}\" not found"

/-- aeson's `.:?` followed by `.!= d`: missing or `null` gives `d`. -/
def optField {α : Type} (o : Json) (k : String) (p : Json → Except String α) (d : α) :
    Except String α :=
  match o.getObjVal? k with
  | .ok .null => pure d
  | .ok v => p v
  | .error _ => pure d

/-- `FromJSON String` (Haskell `[Char]`): no "parsing … failed" prefix. -/
def parseString : Json → Except String String
  | .str s => pure s
  | j => throw (expected "String" j)

/-- `FromJSON Text`. -/
def parseText : Json → Except String String
  | .str s => pure s
  | j => throw s!"parsing Text failed, {expected "String" j}"

/-- `FromJSON Bool`. -/
def parseBool : Json → Except String Bool
  | .bool b => pure b
  | j => throw s!"parsing Bool failed, {expected "Boolean" j}"

/-- `FromJSON [a]`: elements in order, the first failure wins. -/
def parseList {α : Type} (p : Json → Except String α) : Json → Except String (List α)
  | .arr xs => xs.toList.mapM p
  | j => throw s!"parsing [] failed, {expected "Array" j}"

/-- `FromJSON (a, b)`: an array of exactly two elements. -/
def parsePair {α β : Type} (p : Json → Except String α) (q : Json → Except String β) :
    Json → Except String (α × β)
  | .arr xs =>
    match xs.toList with
    | [a, b] => do return (← p a, ← q b)
    | l => throw s!"cannot unpack array of length {l.length} into a tuple of length 2"
  | j => throw s!"parsing (a, b) failed, {expected "Array" j}"

/-- `FromJSON (a, b, c)`: an array of exactly three elements. -/
def parseTriple {α β γ : Type} (p : Json → Except String α) (q : Json → Except String β)
    (r : Json → Except String γ) : Json → Except String (α × β × γ)
  | .arr xs =>
    match xs.toList with
    | [a, b, c] => do return (← p a, ← q b, ← r c)
    | l => throw s!"cannot unpack array of length {l.length} into a tuple of length 3"
  | j => throw s!"parsing (a, b, c) failed, {expected "Array" j}"

/-- `FromJSON Int` (64-bit): any integral number in range, whatever its
written form (`1.0`, `1e2`); otherwise aeson's message, with the value as
`Data.Scientific`'s `show` prints it. -/
def parseInt : Json → Except String Int
  | .num n =>
    let fail : Except String Int :=
      throw s!"parsing Int failed, value is either floating or will cause over or \
        underflow {formatScientificGeneric n}"
    let d := 10 ^ n.exponent
    if n.mantissa % d != 0 then fail else
    let v := n.mantissa / d
    if v < -(2 ^ 63) || v ≥ 2 ^ 63 then fail else pure v
  | j => throw s!"parsing Int failed, {expected "Number" j}"

/-- Haskell's `parseMaybe (.: k) o`: the field parsed, or `none` if it is
missing or does not parse. -/
def maybeField {α : Type} (o : Json) (k : String) (p : Json → Except String α) : Option α :=
  match reqField o k p with
  | .ok a => some a
  | .error _ => none

/-! ## Envelope (§2) -/

/-- A parsed request: `id` and `op`, with the whole object kept for the
operation's own fields. -/
structure Request where
  reqId : String
  reqOp : String
  reqRaw : Json

/-- The `FromJSON Request` instance, run by `eitherDecode`, so its messages
carry aeson's path prefix (`Error in $: …`, `Error in $.id: …`). -/
def parseRequest (j : Json) : Except String Request :=
  match j with
  | .obj _ => do
    let rid ← match j.getObjVal? "id" with
      | .error _ => throw "Error in $: key \"id\" not found"
      | .ok v => (parseText v).mapError ("Error in $.id: " ++ ·)
    let rop ← match j.getObjVal? "op" with
      | .error _ => throw "Error in $: key \"op\" not found"
      | .ok v => (parseText v).mapError ("Error in $.op: " ++ ·)
    return ⟨rid, rop, j⟩
  | _ => throw s!"Error in $: parsing Request failed, {expected "Object" j}"

/-- Successful response: `{"id": …, "ok": true, "result": …}`. -/
def mkOk (rid : String) (result : Json) : Json :=
  Json.mkObj [("id", rid), ("ok", true), ("result", result)]

/-- Error response: `{"id": …, "ok": false, "error": {"code", "message", "details"?}}`. -/
def mkErr (rid code msg : String) (details : Option Json) : Json :=
  Json.mkObj [("id", rid), ("ok", false), ("error", Json.mkObj
    ([("code", Json.str code), ("message", Json.str msg)] ++
      match details with
      | some d => [("details", d)]
      | none => []))]

/-- Parse-error response, with no `id` (it could not be read; §6). -/
def mkParseError (err : String) : Json :=
  Json.mkObj [("ok", false), ("error", Json.mkObj
    [("code", "parse_error"), ("message", Json.str err)])]

end Gamen.Service
