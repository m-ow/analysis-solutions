# Contributing

I would be interested in having volunteers “playtest” the companion to see if this can actually be done (and if the helper lemmas or “API” provided in the Lean files are sufficient to fill in the sorries in a conceptually straightforward manner without having to rely on more esoteric Lean programming techniques). Any other feedback will of course also be welcome.

# Building the book locally

Change directory to `analysis`
Build the doc-gen
```
lake exe Analysis:docs
```

Change the working directory to `./book/`
Build:
```
lake exe analysis-book --docgen-url "http://localhost:8000/analysis/docs/"
```

View the book:
```
python3 serve.py
```
then visit `http://localhost:8000`