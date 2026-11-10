import Std.Async.TCP

/-- Uses libuv-backed TCP, like `Std.Http.Server.serve`, so the stub check must reject its binary. -/
@[export libuv_fixture]
def libuvFixture : IO Unit :=
  discard Std.Async.TCP.Socket.Server.mk
