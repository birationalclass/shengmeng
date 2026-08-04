# Sheng Meng · Personal Academic Homepage

Static, bilingual academic homepage for GitHub Pages. The academic section is paper-only and includes recent arXiv records, while AI4Math, AI4Games, the academic journey, and the playable browser game *Frontier Claim* remain independent modules. The design intentionally uses no personal portrait.

## GitHub Pages

1. Create a GitHub repository. For a root personal homepage, name it `<your-github-username>.github.io`.
2. Push the contents of this directory to the repository's `main` branch.
3. In **Settings → Pages**, choose **GitHub Actions** as the source.

The included workflow publishes the static site automatically. The game is available at `/game/`.

## Local preview

Serve this directory with any static HTTP server, for example:

```powershell
python -m http.server 4180
```

Then visit <http://127.0.0.1:4180/>.
