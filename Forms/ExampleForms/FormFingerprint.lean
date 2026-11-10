module

public import Forms.ExampleForms.Registry
public import Forms.Runtime.BrowserProtocol
meta import Forms.Runtime.FormFingerprint

/-- Compatibility fingerprint shared by the example server and compiled browser forms.
The server includes it in form descriptors; the browser rejects descriptors with
a different fingerprint to avoid running stale form code. Computed at build time from
imported `Forms` declarations, their types, and available bodies; it is not a full
fingerprint of the toolchain or dependencies. -/
public def Forms.ExampleForms.formFingerprint : String := form_fingerprint%
