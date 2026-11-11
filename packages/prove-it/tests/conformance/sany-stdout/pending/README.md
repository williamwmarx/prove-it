# Specs pending a recording of the real SANY

Each spec here needs what TLC at d8fb231 prints for it, recorded as `grid.json` records
`tests/recursive-shapes`. From `packages/prove-it`:

    bun scripts/sany-corpus.ts --specs tests/conformance/sany-stdout/pending \
      --classpath <tla2tools built at d8fb231> --record tests/conformance/sany-stdout/pending.json

That runs `tlc2.TLC -nowarning -noGenerateSpecTE -workers 1 -fp 0 -seed 0 <Spec>` with an empty
`<Spec>.cfg`, in a copy of this directory as the working directory.
