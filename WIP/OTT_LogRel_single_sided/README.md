# Single-sided LogRel chain (superseded — reference only)

These seven files are the **original single-sided** logical-relation development
for the OTT Pi fragment (`src/Pyrosome/Lang/OTT/Norm/Pi/`):

    LogRel  LogRelInd  LogRelLemmas  LogRelRed  LogRelSubst  LogRelRen  LogRelFund

They were **superseded** by the two-sided PER-of-conversion relation
(`LogRel2*` in `Norm/Pi/`) per the ConvRel pivot, and were **broken** by the
`nApp`/`nAppI` `(F,B)` annotation refactor (commit `a24ad6d`). Rather than
repair them they were moved out of the build (`WIP/` is not in `_CoqProject`).

**Why kept as reference, not deleted:** they contain renaming/substitution
algebra that is *not* LogRel-specific and that the plan's **Ph2 "renaming
stability"** intends to reuse — notably, in `LogRelRen.v`:

- `ren_Apply_total`, `Apply_ren_comp`, `Apply_ren_comp_sc`, `Apply_ren_decomp`,
  `ren_is_Apply`, `Apply_ren_eq` — the renaming-as-Apply bridge,
- `ne_below_shift`, `ne_below_mono`, `sub_below`/`sub_below_up`/`sub_below_beta`,
  `Apply_ne_below` — scopedness monotonicity + Apply-preserves-scope,

and in `LogRelSubst.v`, the substitution-closure lemmas.

**Caveat when porting:** everything here predates the `(F,B)` annotation, so the
`nApp`/`nAppI` cases use the OLD 2-field shape (`nApp f a`, `Vapp m vf a v`) and
must be re-threaded with `F` (shifted at the cutoff) and `B` (shifted under one
binder) — exactly as done in `Norm/Pi/ApplySubst.v` (`Apply_shift_eq`,
`Apply_cancel`) and `Determinism.v`. Port into a neutral home (e.g. extend
`ApplySubst.v` or add a `RenSubst.v`), not back into a `LogRel*` file.
