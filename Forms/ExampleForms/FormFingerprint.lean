module

public import Forms.ExampleForms.Registry
public import Forms.Runtime.BrowserProtocol
meta import Forms.Runtime.FormFingerprint

/-- Lets the browser reject descriptors from stale form code.
Covers `Forms` declarations, not the toolchain or dependencies. -/
public def Forms.ExampleForms.formFingerprint : String := form_fingerprint%
