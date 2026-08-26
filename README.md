# Sheng Meng · Personal Academic Homepage

Static, bilingual academic homepage for GitHub Pages. The academic section is paper-only and includes recent arXiv records, while AI4Math, the interactive Visual Lab, AI4Games, the academic journey, and the playable browser games *Endless* and *Frontier Claim* remain independent modules. The design intentionally uses no personal portrait.

Live site: <https://birationalclass.github.io/shengmeng/>

## GitHub Pages

1. Create a GitHub repository. For a root personal homepage, name it `<your-github-username>.github.io`.
2. Push the contents of this directory to the repository's `main` branch.
3. In **Settings → Pages**, choose **GitHub Actions** as the source.

The included workflow publishes the static site automatically. Visual Lab is available at `/visuals/`, with browser editions of the Julia-set, chaotic-attractor, and ruled-surface gluing experiments. *Endless* is available at `/endless/`, while *Frontier Claim* remains available at `/game/`.

## Local preview

Serve this directory with any static HTTP server, for example:

```powershell
python -m http.server 4180
```

Then visit <http://127.0.0.1:4180/>.
