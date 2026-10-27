// Dynamic-scenarios explorer (Widgets/Dynamic/Widget.lean). Hand-written ESM,
// no build step. All logic is in Lean: every student action is one
// `dynamicExplorerStep` RPC call carrying the current state and an event, and the
// component draws the `view` JSON that comes back. Calls are chained, so each
// one starts from the state the previous one returned. No polling.
import * as React from 'react'
import { useRpcSession } from '@leanprover/infoview'

const h = React.createElement

// Drawing area. Layout coordinates are in [0, 1] and nodes are at most 0.1
// across, so the node diameter is kept under a tenth of the inner box.
const PAD = 30, LABEL_ROOM = 110, INNER_W = 360, INNER_H = 300, R = 14
const SVG_W = PAD + INNER_W + LABEL_ROOM, SVG_H = PAD + INNER_H + PAD

const px = w => [PAD + w.x * INNER_W, PAD + w.y * INNER_H]

const boxStyle = (border, bg) => ({
  border: `1px solid ${border}`, background: bg, borderRadius: '4px',
  padding: '6px 8px', margin: '6px 0', whiteSpace: 'pre-wrap'
})
const NEUTRAL = boxStyle('var(--vscode-panel-border, #888)', 'var(--vscode-textBlockQuote-background, rgba(127,127,127,0.1))')
const GOOD = boxStyle('#2e7d32', 'rgba(46,125,50,0.15)')
const BAD = boxStyle('#c62828', 'rgba(198,40,40,0.15)')

// Group edges by unordered pair; a pair drawn both ways with the same agents is
// one undirected line, otherwise each direction is an arrow. Dashed edges (joint
// actions left to the model's default successor) are grouped apart.
function edgeGroups(edges) {
  const byPair = new Map()
  for (const e of edges) {
    const dashed = !!e.dashed
    const k = JSON.stringify([e.from, e.to, dashed])
    if (!byPair.has(k)) byPair.set(k, { from: e.from, to: e.to, dashed, labels: [] })
    const g = byPair.get(k)
    if (!g.labels.includes(e.label)) g.labels.push(e.label)
  }
  const out = [], done = new Set()
  for (const [k, g] of byPair) {
    if (done.has(k)) continue
    done.add(k)
    const rk = JSON.stringify([g.to, g.from, g.dashed])
    const rev = byPair.get(rk)
    const same = rev && rev.labels.slice().sort().join() === g.labels.slice().sort().join()
    if (g.from !== g.to && same) {
      done.add(rk)
      out.push({ ...g, directed: false })
    } else {
      out.push({ ...g, directed: g.from !== g.to })
    }
  }
  return out
}

function ModelSvg({ model, onClick }) {
  const pos = new Map(model.worlds.map(w => [w.name, px(w)]))
  const edges = edgeGroups(model.edges).filter(e => pos.has(e.from) && pos.has(e.to))
  const parts = [
    h('defs', { key: 'defs' },
      h('marker', { id: 'dynexp-arrow', viewBox: '0 0 10 10', refX: 10, refY: 5,
                    markerWidth: 6, markerHeight: 6, orient: 'auto-start-reverse' },
        h('path', { d: 'M 0 0 L 10 5 L 0 10 z', fill: 'currentColor' })))
  ]
  edges.forEach((e, i) => {
    const [x1, y1] = pos.get(e.from), [x2, y2] = pos.get(e.to)
    const label = e.labels.join(',')
    const dash = e.dashed ? '4 3' : undefined
    if (e.from === e.to) {
      // A dashed loop goes below the node, so it never hides a solid one above.
      const s = e.dashed ? -1 : 1
      const top = y1 - s * (R - 1), ctrl = y1 - s * (R + 22)
      parts.push(h('g', { key: `e${i}` },
        h('path', { d: `M ${x1 - 6} ${top} C ${x1 - 18} ${ctrl}, ${x1 + 18} ${ctrl}, ${x1 + 6} ${top}`,
                    fill: 'none', stroke: 'currentColor', strokeOpacity: 0.6, strokeDasharray: dash }),
        h('text', { x: x1, y: e.dashed ? y1 + R + 28 : y1 - R - 19, fontSize: 10, textAnchor: 'middle' },
          label)))
      return
    }
    const dx = x2 - x1, dy = y2 - y1, len = Math.hypot(dx, dy) || 1
    const ux = dx / len, uy = dy / len
    // A directed edge with a reverse partner is offset sideways so both show.
    const off = e.directed ? 4 : 0
    const sx = x1 + ux * R - uy * off, sy = y1 + uy * R + ux * off
    const ex = x2 - ux * R - uy * off, ey = y2 - uy * R + ux * off
    parts.push(h('g', { key: `e${i}` },
      h('line', { x1: sx, y1: sy, x2: ex, y2: ey, stroke: 'currentColor', strokeOpacity: 0.6,
                  strokeDasharray: dash, markerEnd: e.directed ? 'url(#dynexp-arrow)' : undefined }),
      h('text', { x: (sx + ex) / 2 - uy * 8, y: (sy + ey) / 2 + ux * 8 + 3,
                  fontSize: 10, textAnchor: 'middle' }, label)))
  })
  model.worlds.forEach((w, i) => {
    const [x, y] = pos.get(w.name)
    parts.push(h('g', { key: `w${i}`, style: { cursor: 'pointer' }, onClick: () => onClick(w.name) },
      h('title', null, w.clicked ? `${w.name} (selected)` : w.name),
      h('circle', { cx: x, cy: y, r: R,
                    fill: w.clicked ? 'rgba(255,193,7,0.85)' : 'var(--vscode-editor-background, white)',
                    stroke: 'currentColor', strokeWidth: w.clicked ? 3 : 1.5 }),
      h('text', { x: x + R + 4, y: y - 1, fontSize: 12 }, w.name),
      h('text', { x: x + R + 4, y: y + 11, fontSize: 10, fillOpacity: 0.75 },
        w.facts.length ? w.facts.join(', ') : '∅')))
  })
  return h('svg', { width: SVG_W, height: SVG_H, viewBox: `0 0 ${SVG_W} ${SVG_H}`,
                    style: { color: 'var(--vscode-editor-foreground)', fill: 'currentColor',
                             maxWidth: '100%' } }, parts)
}

function Checks({ checks }) {
  if (!checks.length) return null
  return h('table', { style: { borderCollapse: 'collapse', margin: '6px 0' } },
    h('tbody', null, checks.map((c, i) =>
      h('tr', { key: i },
        h('td', { style: { paddingRight: '12px', fontFamily: 'monospace' } }, c.formula),
        h('td', null, c.error !== undefined ? `error: ${c.error}`
                       : (c.worlds.length ? `true at ${c.worlds.join(', ')}` : 'true nowhere'))))))
}

export default function DynamicExplorer(props) {
  const rs = useRpcSession()
  const [result, setResult] = React.useState({ state: props.state, view: props.view })
  const [draft, setDraft] = React.useState(props.view.formulaText || '')
  const [rpcError, setRpcError] = React.useState(null)
  const latest = React.useRef(result)
  const chain = React.useRef(Promise.resolve())
  // State is seeded from props once and never reset from them, as ProofWidgets'
  // InteractiveSvg does: the infoview re-parses props into new objects whenever
  // it re-fetches widgets (e.g. a cursor move), and a reset would wipe progress.

  const send = event => {
    chain.current = chain.current.then(async () => {
      try {
        const r = await rs.call('dynamicExplorerStep', { state: latest.current.state, event })
        latest.current = r
        setResult(r)
        setRpcError(null)
        // Typing keeps the local draft; any other event may clear the text.
        if (!(typeof event === 'object' && 'setFormula' in event)) setDraft(r.view.formulaText || '')
      } catch (e) {
        setRpcError(e && e.message ? e.message : JSON.stringify(e))
      }
    })
  }

  const v = result.view
  const q = v.question
  const kids = []
  kids.push(h('h3', { key: 'title', style: { margin: '4px 0' } }, v.title))
  if (v.setup) kids.push(h('p', { key: 'setup', style: { margin: '4px 0' } }, v.setup))

  kids.push(h('div', { key: 'controls', style: { margin: '6px 0' } },
    v.controls.map(c => h('label', { key: c.key, style: { marginRight: '12px' } },
      h('input', { type: 'checkbox', checked: c.on,
                   onChange: () => send({ toggleControl: { key: c.key } }) }),
      ' ', c.label)),
    h('button', { onClick: () => send('apply'), style: { marginLeft: '8px' } }, 'Apply'),
    h('button', { onClick: () => send('reset'), style: { marginLeft: '4px' } }, 'Reset'),
    h('span', { style: { marginLeft: '12px', opacity: 0.75 } },
      v.applied ? 'Showing the model after the update.' : 'Showing the model before the update.')))

  if (v.applied && v.notes.length)
    kids.push(h('div', { key: 'notes', style: NEUTRAL }, v.notes.join('\n')))

  kids.push(h(ModelSvg, { key: 'svg', model: v.model,
                          onClick: name => send({ clickWorld: { w: name } }) }))
  kids.push(h(Checks, { key: 'checks', checks: v.checks }))

  if (q) {
    const qkids = [
      h('div', { key: 'nav', style: { marginBottom: '4px' } },
        h('button', { onClick: () => send('prevQuestion'), disabled: q.index === 0 }, '◀'),
        h('span', { style: { margin: '0 8px' } }, `Question ${q.index + 1} of ${q.count}`),
        h('button', { onClick: () => send('nextQuestion'), disabled: q.index + 1 >= q.count }, '▶')),
      h('div', { key: 'prompt', style: { margin: '4px 0' } }, q.prompt)
    ]
    if (q.kind === 'writeFormula')
      qkids.push(h('input', { key: 'formula', type: 'text', value: draft, size: 40,
        style: { fontFamily: 'monospace', marginRight: '6px' },
        onChange: ev => { setDraft(ev.target.value); send({ setFormula: { text: ev.target.value } }) },
        onKeyDown: ev => { if (ev.key === 'Enter') send('submit') } }))
    else if (q.kind === 'clickWorlds')
      qkids.push(h('span', { key: 'hint', style: { marginRight: '6px', opacity: 0.75 } },
        'Click worlds in the diagram, then'))
    else if (q.kind === 'reachGoal')
      qkids.push(h('span', { key: 'hint', style: { marginRight: '6px', opacity: 0.75 } },
        'Choose the controls above, then'))
    qkids.push(h('button', { key: 'check', onClick: () => send('submit') }, 'Check'))
    kids.push(h('div', { key: 'question', style: { margin: '8px 0' } }, qkids))
  }

  if (v.feedback)
    kids.push(h('div', { key: 'feedback', style: v.feedback.correct ? GOOD : BAD },
      (v.feedback.correct ? '✓ ' : '✗ ') + v.feedback.message))
  if (v.message) kids.push(h('div', { key: 'message', style: NEUTRAL }, v.message))
  if (rpcError) kids.push(h('div', { key: 'rpc', style: BAD }, `Server error: ${rpcError}`))

  return h('div', { style: { fontFamily: 'var(--vscode-font-family, sans-serif)' } }, kids)
}
