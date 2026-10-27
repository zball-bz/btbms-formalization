# Codex cross-check 1 — T-005

I checked both questions directly against the paper. I did not read `tracker/review/claude-review.md`, `tracker/GAPS.md`, or the gap ledger. The domain decision is understood: Lean's total FS will mirror the reference, including the empty self-loop and reference stopping rule; agreement with the paper is a separate theorem on nonempty V∧I inputs, with decrease/descent explicitly nonempty. No change to the earlier review is made here.

## Q1 — the base case S₀

**Answer:** the argument is valid. The general factorization lemma and complete-certificate capture machinery are stronger than this case needs. Replace their invocations by a direct finite bound and reflection of one elementary existence formula. The source-derived Σ₁ elementarity still supplies an essential fact: arbitrarily high limit ordinals below u. Being a limit ordinal alone does not supply that fact.

**Evidence and replacement.** Let the packet's host be ρ, its owner u, its prescribed floor L<u, its low certificate `w_low∈J_u`, and its supplied target heads `R(u,ρ,p_o)` and `R(u,ρ,p_v)` (`paper.txt:1045`, §7.1). The target is empty, so its only fresh role is its new owner.

1. By continuity choose β<u with `w_low∈J_β`. Let d<u bound L, β, ρ, ω and the finitely many low coordinates, and put `L*=d+1<u`. The last strict inequality uses that u is limit. This directly establishes the floor part of factorization, including **ρ<L***, without invoking its general compatibility conclusion (`paper.txt:1070`, §7.2).
2. The strict source is nonempty. Its first ordinary coordinate b satisfies u<b and `J_u≺Σ₁J_b`: its first column's first parent is the direct owner by V,I, and its visible-parent control edge yields this elementarity (`paper.txt:1190`–1200, §8.1). Since b is a limit coordinate, u∈J_b by the ordinal-height statement (`paper.txt:801`, §5.1).
3. In J_b, u witnesses `∃s (Lim(s) ∧ L*<s)`. This is Σ₁: ordinalhood, being a limit, and the inequalities are bounded conditions. Its parameters L* and ω belong to J_u. Direct Σ₁ elementarity and bounded absoluteness therefore produce an actual s∈J_u with `ω<s`, s limit, and `L*<s`. Thus **ρ<L*<s<u**. Neither the whole J_u nor a record containing u is a fixed parameter. No general complete-certificate capture theorem is needed for this formula.
4. Restrict both supplied heads to environment s (`paper.txt:867`, §5.2). For each selector p, all required conditions hold: p<ρ<s≤u, all three edge coordinates are limit, and the lower endpoints remain unchanged. We obtain both `R(s,ρ,p_o)` and `R(s,ρ,p_v)`; coincident selectors cause no problem.
5. Use a fresh owner name with value s and retain the complete prescribed frame. There are no internal roles or internal elementary pairs in an empty height. The new owner exceeds the original floor, the host and every low coordinate. Old labels keep their old arguments and cannot read this fresh name. The assignments agree on the entire shared frame; no elementary pair is required across a height attachment or between sibling heights. This checks compatibility directly, rather than appealing to the full factorization conclusion.
6. The positive block's maximum is s, so its certificate belongs to `J_{s+ω}⊆J_u` (`paper.txt:878`, §5.2; `paper.txt:737`, §5.1). Also `w_low∈J_β⊆J_s`; the history through β belongs to `J_{β+ω}⊆J_s`. The finite joint record can therefore be packed in `J_{s+ω}⊆J_u`, preserving all low resources. This is the requested positive certificate above L*≥L.

The paper's floor increase must not simply be deleted: **ρ<s** is necessary for restricting the heads. Taking s=ρ violates that strict condition; taking s=u violates the requirement that the certificate lie in J_u. Nor does `s=L*+ω` always give s<u: the bare ordinal conditions allow `u=ω·2`, `L*=ω+1`, with no intermediate limit. That example is not an admitted source packet; it shows why the limit/floor conditions alone cannot replace the source-derived elementarity. One can package its consequence as “limit ordinals are cofinal in u,” but that consequence still needs proof.

**Verdict:** no-gap

## Q2 — exact inductions and reads across scopes

**Answer:** the stated numerical orders suffice, including reverse capping. A formalizer must make the simultaneous quantification over occurrences/scopes explicit and localize the barrier proof. For reverse capping, an effective predicate proves actual entry assertions **together with actual return bounds**. A first-divergence argument then avoids assuming that an arbitrary capped edge already agrees with its uncapped edge. These are proof elaborations derivable from the stated definitions, not additional hypotheses.

### Common notation and scope discipline

Fix the finite expression and a visible-stack context σ. A printed number denotes its particular occurrence in σ, as specified at `paper.txt:65`, §1.1. Write `g_W^σ` for a scan response and `Path_W^σ(x,y)` for a finite path, allowing the reflexive path. Every edge strictly lowers the printed number by V. Restricting σ to the prefix through a visited column leaves all its lower visible occurrences unchanged; a path cannot jump into a closed sibling height.

For a column occurrence c with m entries, write `B_c(i)=ν(K_0,...,K_i)` and `B_c(-1)=∅`. At cut k, 0≤k≤m, put

```
W(c,k) = B_c(k−1)
x(c,k) = c−1                  if k=0,
         parent of entry k−1  if k>0.
```

The case c=0 causes no predecessor-read issue: V permits no entry there, and its empty column has no outgoing scan edge. For a containing entry e at host a and index u, let H_e be its height and `D_e=B_a(u)`. “Containing” refers to actual occurrence containment, not merely a smaller printed number.

The orders below are strong induction on ℕ or on lexicographically ordered ℕ×ℕ. They quantify **simultaneously over every occurrence and compatible scope** with the indicated number. Equal numbers in different scopes are different objects; no induction call uses one as earlier merely because its depth-first position differs.

### Path nesting — `paper.txt:194`–200, §2

**Predicate at c:** for every compatible σ, every column occurrence of number c, every reduced W≤Z and every p, under V,A,

```
g_Z^σ(c)=p  ⇒  Path_W^σ(c,p).
```

**Order:** strong induction on c.

If the W and Z cursors are j≤i, start with the W-edge to p_j. For each j<k≤i, A supplies a path from p_{k−1} to p_k at query `B_c(k−1)>W`. Every vertex used as an edge source on these paths is below c, because every parent is below c and further edges decrease. Apply the induction hypothesis at that source number to replace each edge by a W-path, and concatenate. If j=i, the original one-edge response already agrees. The induction ranges over all queries and scopes, so neither a changed query nor an enclosing-height read escapes its hypothesis. No call to an assertion at number ≥c occurs.

### Barrier — `paper.txt:205`–219, §2

Fix a containing entry e=(a,u,H_e). For each descendant column occurrence c and cut k, use the joint predicate:

- **C_e(c,k):** if an actual `g_{W(c,k)}` path starting at x(c,k) reaches a, then `W(c,k)<D_e`.
- **R_e(c,k), when k<m:** if entry k has parent a, then `B_c(k)<D_e`.

**Order:** strong lexicographic induction on (c,k); prove C first, then R at the same pair. Quantify over all containing entries e and all scopes. Assume actual V,A,S.

To prove C, if the path starts at a, then either k=0 and W=∅<D_e, or k>0 and the preceding entry is a return to a: use R_e(c,k−1). Otherwise the last edge into a is z→a with a<z<c. If it selects entry v, the scan-boundary lemma gives `W<B_z(v)`, and the smaller-column assertion R_e(z,v) gives `B_z(v)<D_e`. Every visible z>a on this path is still inside H_e, so the indicated return assertion is about the same containing occurrence.

To prove R, A at (c,k) says its pre-entry cut path reaches parent a. Hence C gives `B_c(k−1)<D_e`. S gives `K_k<h_a(H_e)`, and the word observation at `paper.txt:211` yields `B_c(k)<D_e`.

This explicitly includes the full cut k=m: only C is then needed, and its same-column dependency is the last return assertion at m−1. The order covers every call: either the column number strictly falls, or it is the same occurrence and the entry index falls.

**Useful localized consequence:** C_e(c,k) needs only the earlier return bounds just listed. It does **not** need A at the prospective entry (c,k), or any later entry. This is the precise form needed in reverse capping.

### Capping — `paper.txt:220`–236, §2

Fix a selection of last-entry keys on the terminal containment route, replaced independently by ⊤. Let “actual” refer to the unchanged explicit heights and “decorated” to those assigned keys.

Two consequences of the definition are important:

1. An entry's own pre-entry query is identical in the actual and decorated systems: a changed key is last in its column and therefore absent from every entry's preceding prefix. Independently assigned descendant keys do not change a containing entry's explicit height key.
2. If a capped column a is visible while checking an entry in column c>a, a is a containing column of that entry. A different closed sibling's column cannot both lie on the global terminal route and be visible here. Let v be the index of the containing entry currently active at a, and u* its capped last index. It is possible that v<u*, but always v≤u*.

**Forward direction:** actual A and the barrier give `W<B_a(v)≤B_a(u*)` whenever a cut path reaches a visible capped column a. The actual cursor is therefore at or before v, and raising the last key cannot change its response. Following the path preserves each edge and proves decorated A. This uses the actual barrier already proved; no reverse assertion is assumed.

**Reverse induction predicate at (c,i):** assuming V,S and global decorated A, prove, simultaneously for all occurrences/scopes,

- actual A for entry i of column c; and
- for every containing entry e whose host equals this entry's parent, the **actual** return bound R_e(c,i).

**Order:** strong lexicographic induction on (c,i), with 0≤i<m. The actual query W(c,i) equals the decorated query by point 1.

Before proving actual A(c,i), use the earlier return bounds and the localized barrier argument to establish C_e(c,i) for every containing e. Follow the decorated A-witness and suppose there is a first edge that differs from the actual scan response. Its source a must be a capped column. The preceding path segment is already actual and reaches a. By point 2, a has a currently active containing entry v≤u*. Therefore C gives

```
W < B_a(v) ≤ B_a(u*)                 (all boundaries actual).
```

The actual scan stops at or before v≤u*. Changing only the last key to ⊤ preserves that cursor and its returned parent, contradicting the supposed first differing edge. Thus the whole witness is an actual path and actual A(c,i) holds. Now use actual A(c,i), the localized barrier and S exactly as in the previous R-step to establish the current actual return bounds. This closes the simultaneous induction.

This argument does **not** infer `W<B_z(v)` in the actual system merely from a decorated edge: that inference would be invalid if the selected key were ⊤. The first-divergence construction supplies an already-actual incoming path before invoking the localized actual barrier. That is the needed expansion of “Those earlier entry assertions have already been uncapped” (`paper.txt:228`).

Finally, the definedness conclusion uses the ordinary actual barrier at the stopping return: `Z<ν(Z⌢[∅])<B_r(u)` (`paper.txt:233`–236). Thus an owner-root scan cannot be exhausted. V,I supply the legal route/root conditions; this is separate from the reverse-capping induction and does not require well-foundedness of the syntax order.

### What the formalizer must add

The paper does not print these quantified joint predicates, the localized pre-entry-cut barrier, or the first-divergence argument as separate lemmas. They should be written explicitly. A proof that carries only “earlier entry A holds” and then directly substitutes actual for decorated selected boundaries would leave a gap. However, the strengthening above follows from the paper's own barrier proof and terminal-route visibility definitions, uses precisely its stated numerical order, and needs no new assumption or inaccessible induction hypothesis. I therefore do not identify an unrepaired mathematical gap in any of the three proofs.

**Verdict:** no-gap

STATUS: COMPLETE
