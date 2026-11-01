# Turmite Explorer

A single-page visualizer for Terminating Turmites (TT) and Tooting Terminating Turmites (TTT).
It has no dependencies or build step: `index.html` is the whole tool, and `404.html` makes
`/explore/<machine>` URLs work on GitHub Pages.

## URLs

    <site>/explore/1TB---_1PA0PB            a TT (halting time)
    <site>/explore/1TA2PA3PA4PA---;A4       a TTT: machine;toot transition
    <site>/?m=0TB0PB_1TB1PA;A1              the same, as a query parameter
    index.html#0TB0PB_1TB1PA;A1             when opened as a local file

## What it shows

* **Last toot / TTT value.**  A decider runs in a Web Worker (default 10⁷ steps; adjustable).
  It is a JavaScript port of `../ttt.c`: halting, cyclers (Brent) and translated cyclers
  (records with equal tape over the period's excursion).  The value is shown as
  * *final* when the machine halts, or when it settles into a repeating period that does not
    use the toot transition;
  * *∞ (toots forever)* when the toot transition is in the period;
  * *so far* when the run is undecided within the step limit (e.g. bouncers, counters, chaotic
    machines; see `../../../ttt.md` for proofs about those).
* **Transition table.**  Uses and last use of every transition, with `∞` on the transitions of
  the repeating period and the toot transition outlined.  Without a toot transition, each last
  use is what the TTT value would be with that toot.
* **Space-time diagram.**  One row per configuration (after `t` steps), cells coloured by
  symbol, the head drawn as a triangle pointing the way it faces (colour = state).  An orange
  mark in the left margin means the toot happens in the next step (or within the next *k* steps
  with *k* steps per row).  Options: start step, rows, steps per row, cell size, and columns
  (the whole visited tape or the head's range in view).  "Go to last toot" centres the view on
  it.  Hover a row to see its configuration and the next transition.

Conventions: the head starts in state A facing right on a blank tape; `P` moves one cell the
same way as the last move, `T` turns around and moves one cell; `---` (or a target beyond the
last state, such as `Z`) halts, and the halting step counts.

## Hosting on GitHub Pages

The `gh-pages` branch of this repository holds a copy of this folder (`index.html`, `404.html`,
`.nojekyll`).  Enable it under Settings → Pages → Build and deployment → Deploy from a branch →
`gh-pages` / `(root)`; the explorer is then at `https://<owner>.github.io/<repo>/`.  To update
it, copy this folder's files to that branch again.

Local use: open `index.html` directly, or serve the folder (`python3 -m http.server`) and visit
`http://localhost:8000/?m=1TB---_1PA0PB`.
