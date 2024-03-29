# Code Style Guide

### General Rules

* Maximal line length should not exceed 80 characters.

### Naming conventions

* Prefer `snake_case` for the names of function arguments, inductive datatypes, definitions, and lemmas.

* Prefer `CamelCase` for the names of hypothesis, variables inside sections, modules, and sections.

```Coq
Module Foo.

  Section Bar.

    Variable Hb : bool.

    Definition lt_zero x := x < 0.

    Inductive tri_bool :=
    | tri_true
    | tri_false
    | tri_unknown

    Lemma lt_zero_lt_one x (HLtZ : lt_zero x) :
      x < 1.
    Proof. admit. Admitted.

  End Bar.

End Foo.

```

* Use the following conventions for naming variables.

  * For names of **events** use `e`, `e'`, `e1`, `e2`, `e3` etc.
    If it is known from the context that event has a specific type
    (i.e. it is a read, write or fence) use the corresponding names
    to highlight that: `r`, `w`, `f` etc.

  * For names of **labels** use `l`, `l'`, `l1`, `l2`, `l3` etc.
    If it is known from the context that label has a specific type
    (i.e. it is a read, write or fence label) add the corresponding suffix
    to highlight that and use names: `lr`, `lw`, `lf` etc.

  * Use the last letters of latin alphabet for names
    of **memory locations (variables)**: `x`, `y`, `z`.

  * Use the first letters of latin alphabet for names
    of **values**: `a`, `b`, `c`, etc.

* Prefer short names for binary relations, in the style of weak memory papers
  (ideally, two to four letters in length).
  Give the full name in a comment near the definition of the property.

  ```Coq
    (* Causality relation *)
    Definition ca := connect ica.
  ```

* Use the following common prefixes and suffixes.

  * `o` prefix for **option-valued** functions,
    e.g. `omap`, `obind` from `ssrfun.v`.

  * `f` prefix for **functional** (computational) version of a relation,
    e.g. `fpred`, `frf`, etc.

  * `s` prefix for **strict** (irreflexive) version of some partial order,
    e.g. `sca` for strict causality.

  * `i` prefix for **immediate**, non-transitive version of a relation,
    e.g. `ica`, `icf`, etc.

* To name a lemma stating a property of some function or relation
  use name of function/relation followed by the name of property, e.g.
  `ca_trans`, `cf_irrefl`, etc.

### Indentation and Spaces

* Use two spaces to indent a new block (do not use tabs).

* Always indent a content of the `Module` and `Section` (see example above).

* Start a proof on a new line and indent a content of the `Proof` block,
  except when the proof is short and can fit into one line.

```Coq
(* one line proof *)
Lemma lt_zero_lt_one x : x < 0 -> x < 1.
Proof. ssrlia. Qed.

(* multi line proof *)
Lemma le_or_gt_zero x :
  {x <= 0} + {x > 0}.
Proof.
  tac1.
  tac2.
  tac3.
Qed.
```

* When the lemma statement does not fit into single line,
  put some arguments (assumptions) on the new line
  and indent them to the first argument on the previous line.
  In this case also put the conclusion on the new line,
  and indent it with two spaces.
  In such a way that it would be easier to visually
  separate the conclusion from the assumptions.
  An example is given below.

```Coq
Lemma upd_ord_max {T : nat -> Type} {n}
                  (f : forall m : 'I_n, T m) (x : T n) :
  upd f x ord_max = x.
```

* View intro patterns should be separated by spaces, e.g. `move /eqP /andP`.

* Binary operators should be surrounded by spaces: `t : T`, `a := 2 + 2`, `A -> B` etc.
  The **statement of the lemma** is **not an exception**.
  That is always surround `:` in the statement of lemma by spaces
  (see examples above).
  There are some exceptions to this rule mentioned below.

* SSReflect tacticals, i.e. `:`, `=>`, etc,
  should not be separated from the preceding tactic:
  `move=>`, `case:`.

* The `;` tactical should not be separated from the preceding tactic: `apply Hx; auto`.

* When using goal selectors, do not separate goal numbers by spaces
  and do not put spaces before `:`.

```Coq
apply Hx.
1,2,3: omega.
all: congruence.
```

* Separate conjuncts by single space. Also surround disjuncts separator  `|` by spaces.
  But do not put spaces after opening bracket `[` or before closing bracket `]`.

```Coq
case: HAnd=> [HA HB].
```

```Coq
case: HOr=> [HA | HB].
```

```Coq
case: HExist=> [x Hx].
```

```Coq
case: HOption=> [|H].
```

* Same rules apply when using `[|]` to handle subgoals by different tactics.

```Coq
apply Hx; [apply Hy | apply Hz].
```

```Coq
apply Hx; [apply Hy |].
```

* When tactics used to handle subgoals do not fit into one line,
  use the indentation style as in the example below.

```Coq
apply Hx;
  [ apply Ha
  | apply Hb
  | apply Hc
  ].
```

### Goal bookkeeping

* Use curly brackets `{}` instead of bullets `+`, `-`, `*`, etc in order to focus on the subgoal.

* Put a space after opening bracket `{` and before closing bracket `}`.

* When selecting a subgoal with brackets always start the subgoal's proof on a new line and use indentation.

* Do not leave opening `{` or closing bracket `}` alone on a line.

* Do not focus the last subgoal (rule of thumb: there're no two `}` on the line and there's no `}` preceding `Qed.`).

```Coq
apply Hx.
{ ssrlia. }
{ apply Ha.
  apply Hb. }
apply Hy.
```

* Avoid references to the autogenerated names like `H0` when possible.

### Proof's style

* Do not use long one-liners in proofs. Do not abuse `;` tactical.
  In particular, do not try to put several proof steps into one line.
  Instead, each proof step should end with `.` and be held on a separate line.
  These rules are necessary for proof maintenance and modification.
  Otherwise, it becomes harder to go through proofs in interactive mode
  and, on modifications, find the exact place where proof breaks.
