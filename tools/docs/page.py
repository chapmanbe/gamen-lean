"""The page shell shared by every page of the documentation site.

`depth` is how many directories below the site root the page sits (0 for
`index.html`, 1 for `notebooks/X.html`), so relative links work both on
GitHub Pages and from a local `_site/` folder.
"""
from html import escape

REPO_URL = "https://github.com/chapmanbe/gamen-lean"


def page(title: str, body_html: str, depth: int) -> str:
    up = "../" * depth
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{escape(title)}</title>
<link rel="stylesheet" href="{up}site.css">
</head>
<body>
<header class="site-header">
  <a class="site-name" href="{up}index.html">gamen-lean</a>
  <nav>
    <a href="{up}index.html">Home</a>
    <a href="{up}api/index.html">API reference</a>
    <a href="{up}notebooks/index.html">Notebooks</a>
    <a href="{REPO_URL}">GitHub</a>
  </nav>
</header>
<main>
{body_html}
</main>
</body>
</html>
"""
