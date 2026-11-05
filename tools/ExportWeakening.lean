module

import Tests.Weakening

-- Load executable code for `lean --run`.
meta import Tests.Weakening

public def main (args : List String) : IO Unit :=
  IO.println (if args.contains "basket" then Tests.Weakening.basketSpec else Tests.Weakening.reportSpec)
