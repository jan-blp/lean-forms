import Tests.Weakening

def main (args : List String) : IO Unit :=
  IO.println (if args.contains "basket" then Tests.Weakening.basketSpec else Tests.Weakening.reportSpec)
