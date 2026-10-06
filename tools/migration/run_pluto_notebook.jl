using Pluto
path = ARGS[1]
session = Pluto.ServerSession()
nb = Pluto.SessionActions.open(session, path; run_async=false)
nerr = 0
for c in nb.cells
    if c.errored
        global nerr += 1
        println("CELL ERROR: ", first(split(string(c.output.body), "\n"), 1))
    end
end
println("cells=", length(nb.cells), " errored=", nerr)
Pluto.SessionActions.shutdown(session, nb)
