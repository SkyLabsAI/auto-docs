# SkyLabs Auto Docs

To install dependencies, run

```sh
npm install
```

To serve the website and watch for changes, run

```sh
npm run watch
```

### Input syntax

To add a new tutorial:

- Create a folder under `fmdeps/micro-docs/content/docs/`
- Add a `foo.v` file with the content, and a `foo.11tydata.json` file with
metadata: the title is used at the top of the document, and
`tags`/`requires`/`provides` are metadata that is not used yet.

The `.v` files are converted to HTML by using syntax highlighting on the Rocq code.

Comments using `(*| Markdown Text with LiquidJS Tags |*)` are converted to paragraphs
"outside" the code blocks; probably avoid such comments "inside" Rocq sentences,
the output is odd.

The syntax can use Liquid Tags http://liquidjs.com/tags/overview.html.

You can also hide Rocq code from the output as follows:

```
(*@HIDE@*)
... whole Rocq sentences to hide from output.
(*@END-HIDE@*)
```
