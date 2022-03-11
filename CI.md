In this project, continuous integration is based on Github Actions.
For now we rely on https://github.com/coq-community/templates to generate
the action from the `meta.yml` file. Actually the `coq-ssprove.opam` file is
also generated from it.

## With bash

```bash
TMP=$(mktemp -d); git clone https://github.com/coq-community/templates.git $TMP
$TMP/generate.sh .github/workflows/docker-action.yml coq-ssprove.opam
```

## With fish

```fish
set TMP (mktemp -d) ; git clone https://github.com/coq-community/templates.git $TMP
$TMP/generate.sh .github/workflows/docker-action.yml coq-ssprove.opam
```