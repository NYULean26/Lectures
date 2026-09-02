# Computer assisted formalization of mathematics

This repo contains the Lean files used for the lectures of the course DS-GA 3001 · 007 / MATH-GA 2650, Computer assisted formalization of mathematics.

## Live Lean links

Install the small URL-builder dependency once:

```sh
npm install
```

Then build a compressed [Live Lean](https://live.lean-lang.org/) link from any Lean file:

```sh
npm run live-url -- "Week 01/Lecture01.lean"
```

The utility can also decode a `codez` URL:

```sh
npm run live-url -- --decode 'https://live.lean-lang.org/#codez=...'
```
