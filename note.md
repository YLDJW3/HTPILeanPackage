# Intro
1. intro hypotesis
    1. `asuume h: {hypothesis}`
    2. `have h: {hypothesis} := {proof of h}`
2. finish proof
    1. `show {Goal} from {proof}`
    2. `exact h` if current goal is h
3. laws of logic
    1. `contrapos`
        change from $P\rightarrow Q$ to $\neg Q\rightarrow\neg P$
    2. `demorgan`
        change from $\neg(P\land Q)$ to $\neg P \lor \neg Q$
    3. `conditional`
        change from $P\rightarrow Q$ to $\neg P\lor Q$
    4. `double_neg`
        change from $\neg\neg P$ to $P$
# Ch3 Proofs
## 3.1&3.2 Proofs Involving Negations and Conditionals
1. To prove a goal of form $P \rightarrow Q$
    1. `assume h: P` add a given `h` and change the goal to `Q`
    2. `contrapos` change the goal to $\neg Q\rightarrow \neg P$
2. To prove a goal of form $\neg P$
    1. rewrite the goal with logical laws: `demorgan`, `conditional`, `double_neg`, `bicond_neg`
    2. `by_contra h`: add the negation of current goal as a hypothesis `h`, then prove `False` 
    3. `absurd h1 h2`: if h1, h2 are negation of each other, this will finish the proof
3. To use a given of form $\neg P$
    1. `contradict h` set the negation of h as goal to prove False 
    2. rewrite given with logical laws like `demorgan`
4. `apply h`
    If current goal is $Q$, and we have given $h: P\rightarrow Q$, `apply h` changes the goal to $P$
## 3.3 Proofs involving Quantifiers
1. $\forall$
    1. To prove a goal of $\forall (x: U), P\ x$ 
    `fix x: U` intros x and changes the goal to `P x`
    2. To use a given $h: \forall (x: U), P\ x$
    apply it to `a` of type U, `have h1: P a := h a`
2. $\exists$
    1. To prove a goal of $\exists (x: U), P\ x$
    `exists x` or `apply Exists.intro x _`, then prove `P x`
    2. To use a given $h: \exists (x: U), P\ x$
    `obtain (u : U) (h' : P u) from h` adds a new given `h'`
3. `quant_neg` tactic
    1. $\neg\forall(x: U), P\ x$ changes to $\exists(x: U), \neg P\ x$
    2. $\neg\exists(x: U), P\ x$ changes to $\forall(x: U), \neg P\ x$
4. `define`
    use `define` tactic to write out the definition
5. union and intersection
    1. Union of a family of sets $\cup F$, `\U0` in lean
    2. Intersection of a family of sets $\cap F$, `\I0` in lean
## 3.4 Proofs involving Conjunctions and Biconditionals
1. $\land$
    1. To prove a goal of $P \land Q$, `apply And.intro`, then prove `P` and `Q` respectively
    2. To use a given of $h: P \land Q$, use `h.left` as a proof of `P`, or use `h.right` as a proof of `Q`
2. $\leftrightarrow$
    1. To prove a goal of $P \leftrightarrow Q$, `apply Iff.intro` then prove $P \rightarrow Q$ and $Q \rightarrow P$
    2. To use a given of $h: P \leftrightarrow Q$, `h.left` is the proof of $P \rightarrow Q$, and `h.right` is the proof of $Q \rightarrow P$
3. calculational proof
    1. `calc` tactic
    2. **and_assoc**: `{a b c : Prop} : (a ∧ b) ∧ c ↔ a ∧ b ∧ c`
4. `Set.ext`
```lean
@Set.ext : ∀ {α : Type u_1} {a b : Set α},
            (∀ (x : α), x ∈ a ↔ x ∈ b) → a = b
```
## 3.5 Proofs involving Disjunctions
1. To use a given of the form $h: P \lor Q$
    `by_cases on h`
2. To prove a goal of the form $P \lor Q$
    1. `Or.inl` changes the goal to P
    2. `Or.inr` changes the goal to Q
    3. `or_right with h` adds a give $h: \neg Q$ and changes the goal to `P`
    4. `or_left with h` adds a give $h: \neg P$ and changes the goal to `Q`
3. `disj_syll`
    with given `h1: P or Q` and `h2: not P`, `disj_syll h1 h2` can get a proof of `Q`
## 3.6 Existence and Uniqueness Proofs
1. To prove a goal of the form $\exists!(x: U)\ P\ x$
    1. prove $\exists (x: U)\ P\ x$
    2. prove $\forall (x\ y: U)\ P\ x\rightarrow P\ y\rightarrow x=y$
    3. `exists_unique` tactic applies this proof strategy
2. To use a given of the form $\exists!(x: U)\ P\ x$
    `obtain x h1 h2 from h`
2. `union_comm`
    ```lean
    ∀ {U : Type} (X Y : Set U), X ∪ Y = Y ∪ X
    ```
3. `or_comm`
    ```lean
    ∀ {a b : Prop}, a ∨ b ↔ b ∨ a
    ```
4. `apply?` tactic asks Lean to search through its library to see if there's one that could be applied to prove the goal
## 3.7 More Examples of Proofs
1. Numbers
    1. `Nat` is the type of natural numbers 
    2. `Int` is the type of integers
    3. `Rat` is the type of rational numbers
    4. `Real` is the type of real numbers
    5. `Complex` is the type of complex numbers
    Lean also uses the notation ℕ, ℤ, ℚ, ℝ, and ℂ for these types.
2. **Divisibility**
    write `x ∣ y` to mean that x divides y, or y is divisible by x
3. **Reflexivity**
    `Eq.refl`: ∀ {α : Sort u_1} (a : α), a = a
    `Iff.refl`: ∀ (a : Prop), a ↔︎ a
    `rfl` tactic
4. `ring` tactic
    `ring` can combine algebraic laws involving addition, subtraction, multiplication, and exponentiation with natural number exponents to prove many equations in one step
# Ch6 Mathematcial Induction
1. `by_induc`
2. `Sum`
    1. `sum_base`
    ```lean
    ∀ {A : Type} [inst : AddZeroClass A] {k : ℕ} {f : ℕ → A}, 
        Sum i from k to k, f i = f k
    ```
    2. `sum_step`
    ```lean
    ∀ {A : Type} [inst : AddZeroClass A] {k n : ℕ} {f : ℕ → A}, 
        k ≤ n → 
        Sum i from k to n + 1, f i = (Sum i from k to n, f i) + f (n + 1)
    ```
    3. `sum_from_zero_step`
    ```lean
    ∀ {A : Type} [inst : AddZeroClass A] {n : ℕ} {f : ℕ → A}, 
        Sum i from 0 to n + 1, f i = (Sum i from 0 to n, f i) + f (n + 1)
    ```
3. `Nat.mul_le_mul_right`
    ```lean
    ∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
    ```
4. `decide`
    The truth or falsity of the inequality in the base case can be decided by simply doing the necessary arithmetic
5. `linarith`
    The tactic `linarith` makes inferences that involve combining **linear equations and inequalities**

