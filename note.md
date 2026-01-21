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
# Ch6 Mathematical Induction
## 6.1 Proof by mathematical induction
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
## 6.4 Strong induction
1. **Division algorithm**: For all natural numbers n and m, if m > 0 then there are natural numbers q and r such that n = qm + r and r < m
2. **Well-ordering principle**: Every **nonempty** set of natural numbers has a **smallest** element
# Ch7 Number theory
## 7.1 Greatest Common Divisor
1. gcd recursive definition
```lean
def gcd (a b : Nat) : Nat :=
  match b with
    | 0 => a
    | n + 1 =>
      have : a % (n + 1) < n + 1 := mod_succ_lt a n
      gcd (n + 1) (a % (n + 1))
  termination_by b
```
2. gcd_dvd
```lean
theorem gcd_dvd : ∀ (b a : Nat), (gcd a b) ∣ a ∧ (gcd a b) ∣ b
```
3. gcd_lin_comb
```lean
theorem gcd_lin_comb : ∀ (b a : Nat),
    (gcd_c1 a b) * ↑a + (gcd_c2 a b) * ↑b = ↑(gcd a b)
```
## 7.2 Prime Factorization
1. prime
```lean
def prime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬∃ (a b : Nat), a * b = n ∧ a < n ∧ b < n

def prime_factor (p n : Nat) : Prop := prime p ∧ p ∣ n
```
2. exists_prime_factor
```lean
lemma exists_prime_factor : ∀ (n : Nat), 2 ≤ n →
    ∃ (p : Nat), prime_factor p n
```
3. prime factorization
```lean
def prime_factorization (n : Nat) (l : List Nat) : Prop :=
  nondec_prime_list l ∧ prod l = n
```
4. every positive integer has a prime factorization
```lean
lemma exists_prime_factorization : ∀ (n : Nat), n ≥ 1 →
    ∃ (l : List Nat), prime_factorization n l
```
5. prime factorization uniqueness
```lean
theorem Theorem_7_2_5 : ∀ (l1 l2 : List Nat),
    nondec_prime_list l1 → nondec_prime_list l2 →
    prod l1 = prod l2 → l1 = l2
```
6. **fundamental theorem of arithmetic**
```lean
theorem fund_thm_arith (n : Nat) (h : n ≥ 1) :
    ∃! (l : List Nat), prime_factorization n l
```
7. relatively prime
```lean
def rel_prime (a b : Nat) : Prop := gcd a b = 1

theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry
```
## 7.3 Modular
1. congruence classes
```lean
theorem cc_rep {m : Nat} (X : ZMod m) : ∃ (a : Int), X = [a]_m

theorem cc_eq_iff_congr (m : Nat) (a b : Int) :
    [a]_m = [b]_m ↔ a ≡ b (MOD m)

theorem add_class (m : Nat) (a b : Int) :
    [a]_m + [b]_m = [a + b]_m

theorem mul_class (m : Nat) (a b : Int) :
    [a]_m * [b]_m = [a * b]_m
```
2. uniqueness of remainder
```lean
theorem Theorem_7_3_1 (m : Nat) [NeZero m] (a : Int) :
    ∃! (r : Int), 0 ≤ r ∧ r < m ∧ a ≡ r (MOD m)
```
3. congruence class invertibility
```lean
def invertible {m : Nat} (X : ZMod m) : Prop :=
  ∃ (Y : ZMod m), X * Y = [1]_m

theorem Theorem_7_3_7 (m a : Nat) :
    invertible [a]_m ↔ rel_prime m a
```
## 7.4 Euler theorem
1. **Euler’s totient function** $\phi (m)$
    1. defines to be the number of $\Z /\equiv m$ elements of that have multiplicative inverses
    2. $\phi (m)$ is also equal to the number of natural numbers $a < m$ that are relatively prime to $m$
    ```lean
    def num_rp_below (m k : Nat) : Nat :=
        match k with
            | 0 => 0
            | j + 1 => if gcd m j = 1 then (num_rp_below m j) + 1
                        else num_rp_below m j
    def phi (m: Nat) : Nat :=
        num_rp_below m m
    ```
2. Euler's theorem
```lean
theorem Theorem_7_4_2 {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    [a]_m ^ (phi m) = [1]_m
```
3. F product
    1. F-product = (F m 0) * (F m 1) * ... * (F m (m - 1))
    2. the product is equal to the product of all congruence classes `[i]_m` with m and i **relatively prime**
    3. that is the product of all **invertible congruence classes**
    ```lean
    def F (m i : Nat) : ZMod m := if gcd m i = 1 then [i]_m else [1]_m

    def prod_seq {m : Nat} (j k : Nat) (f : Nat → ZMod m) : ZMod m :=
        match j with
            | 0 => [1]_m
            | n + 1 => prod_seq n k f * f (k + n)
    
    prod_seq m 0 (F m) -- denotes the F product
    ```
