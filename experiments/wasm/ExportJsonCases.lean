import Tests.ExpressionProtocol

def main : IO Unit :=
  Tests.ExpressionProtocol.runWith (fun json => IO.println json.compress)
