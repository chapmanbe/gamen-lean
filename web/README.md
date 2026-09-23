# Web editor for the gamen notebooks (local prototype)

`projects/GamenCourse/` is a [lean4web](https://github.com/leanprover-community/lean4web)
project that depends on this repository and offers the notebooks in
`Notebooks/` under the editor's *Examples* menu.

```sh
web/setup.sh       # once: clone lean4web, apply the patch, npm install, build
web/run-local.sh   # then open http://127.0.0.1:3000
```

If the right-hand panel stays on "No info found" after loading an example,
reload the page once (a known first-load issue, not yet diagnosed).

## Security

On macOS there is no bubblewrap sandbox, so Lean code typed into the editor
runs with your user's permissions. lean4web's own `npm start` passes
`vite --host`, which serves the editor to the whole network, and its
server listens on all interfaces. `lean4web-localhost.patch` binds the
server to `HOST` (default 127.0.0.1) and the client to loopback, with the
server port taken from `LEAN4WEB_SERVER_PORT` (default 8090 in
`run-local.sh`). Never expose this setup beyond localhost.

A classroom deployment needs a Linux server with bubblewrap and lean4web's
production mode (`lean4web/doc/Installation.md`).
