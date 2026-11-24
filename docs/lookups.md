# Lookups

A lookup stores a `Reference Key` containing an `id` and `displayText`. Search
results contain `LookupCandidate Key Details` values: a reference and typed `details`
used by the Lean form. The candidate details are not stored in the selected field
or included in the React view.

The JSON response has this shape:

```json
{
  "found": [
    { "reference": { "id": "DE", "displayText": "Germany" }, "details": {} }
  ],
  "more": false
}
```

For `LookupResults String Unit`, every candidate must include `"details": {}`.
Missing `details` and `"details": null` fail to decode. Other details types use their
own JSON encoding. Results must have unique reference keys.

`LookupResults.select` filters candidates using a decidable predicate, rejects
duplicate keys among all matches, then takes the first `limit` matches. `more`
indicates that additional matches were left out. Disabled candidates count toward
the limit.

The lookup's availability computation returns either `.enabled` or
`.disabled reason` for each candidate. Disabled candidates remain visible with
their reason and cannot be chosen. Choosing checks availability again against the
current form state, even when the results were cached.

Availability limits choosing; it does not validate or clear an existing selection.
A previously selected reference can remain saved and be submitted after its
candidate becomes disabled. Add a separate validation rule when a saved selection
must remain eligible. The submit endpoint must independently enforce business
constraints, since the form runs on the client.

To try typed details and disabled candidates, build the native and Wasm targets
as described in the README, then run:

```sh
lake -q exe forms-web business-partners --open
```
