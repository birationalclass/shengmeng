# Pinyon Script

`PinyonScript-Regular.ttf`, by Nicole Fally and Eben Sorkin.

English round hand lettering selected to follow the user’s Copperplate capitals
reference: high stroke contrast, a consistent slope, looped capitals and connected
lowercase. The font is not a tracing or identification of the reference page.

- [Typeface project](https://github.com/SorkinType/Pinyon).
- [Distributed font](https://github.com/google/fonts/tree/main/ofl/pinyonscript).
- Unmodified font, distributed under the SIL Open Font License 1.1;
  see `OFL-PinyonScript.txt`.

The ring verse keeps four explicit lines. Normal letter spacing preserves script
joins; its responsive size fits the complete lines inside the left caption area.

## Consistent opening typography across platforms

The opening also serves these fonts from this directory, without checking fonts
installed on Windows or macOS:

| Runtime family | Original typeface | Included styles |
| --- | --- | --- |
| `OpeningSerif` | [Source Serif 4](https://github.com/adobe-fonts/source-serif) | Regular and true italic, weight 400, optical size 24 |
| `OpeningSans` | [Inter](https://github.com/rsms/inter) | Variable weights 100–900; optical sizing disabled in CSS |
| `OpeningChinese` | [Noto Serif SC](https://github.com/notofonts/noto-cjk) | Regular 400; current semester Chinese text and punctuation |

These WOFF2 files are subsets with renamed font family metadata. Their original
copyright notices and SIL Open Font License 1.1 are preserved in the corresponding
`OFL-SourceSerif4.txt`, `OFL-Inter.txt`, and `OFL-NotoSerifSC.txt` files. No system
font has been copied or redistributed. Pinyon Script remains unchanged.

`opening-fonts-manifest.json` records source hashes, transformations, sizes and
retained codepoints. All subsetting is performed locally from complete upstream
font files; no course text is sent to an external font service. Playback only
accesses this site's files. The loader explicitly waits for the six opening font
faces, including Pinyon Script and the existing STIX math font, before preparing
the animation.

Build dependencies: `fonttools` and `brotli`. Run `build-fonts.py` with a directory
containing these files downloaded from the official Google Fonts repository:

- `SourceSerif4-Roman.ttf`: [SourceSerif4[opsz,wght].ttf](https://github.com/google/fonts/blob/main/ofl/sourceserif4/SourceSerif4%5Bopsz%2Cwght%5D.ttf)
- `SourceSerif4-Italic.ttf`: [SourceSerif4-Italic[opsz,wght].ttf](https://github.com/google/fonts/blob/main/ofl/sourceserif4/SourceSerif4-Italic%5Bopsz%2Cwght%5D.ttf)
- `Inter.ttf`: [Inter[opsz,wght].ttf](https://github.com/google/fonts/blob/main/ofl/inter/Inter%5Bopsz%2Cwght%5D.ttf)
- `NotoSerifSC.ttf`: [NotoSerifSC[wght].ttf](https://github.com/google/fonts/blob/main/ofl/notoserifsc/NotoSerifSC%5Bwght%5D.ttf)
- The three corresponding `OFL.txt` licenses renamed as listed above.

The build scans this semester's `index.html` and `opening*.js` / `opening*.css`.
When adding Chinese text, rerun it to include any new glyphs. Original font source
files are development inputs and are not needed on the website.
