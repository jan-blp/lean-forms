module

import Tests.ExpressionProtocol
meta import Tests.ExpressionProtocol

public def main : IO Unit :=
  Tests.ExpressionProtocol.runWith (fun json => IO.println json.compress)
