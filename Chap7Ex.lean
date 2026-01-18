import HTPILib.Chap7
namespace HTPI.Exercises

/- Section 7.1 -/
-- 1.
theorem dvd_a_of_dvd_b_mod {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := by
    define at h1; obtain k1 h3 from h1; clear h1
    define at h2; obtain k2 h4 from h2; clear h2
    set q := a / b
    have h1: b * q + a % b = a := Nat.div_add_mod a b
    define; exists k1 * q + k2
    calc a
        _ = b * q + a % b := by rw[h1]
        _ = d * k1 * q + d * k2 := by rw[h4, h3]
        _ = d * (k1 * q) + d * k2 := by rw[Nat.mul_assoc]
        _ = d * (k1 * q + k2) := by rw [Nat.left_distrib]
    done

-- 2.
lemma gcd_comm_lt {a b : Nat} (h : a < b) : gcd a b = gcd b a := by
  have g1: b ≠ 0 := by linarith
  have h1 := by apply gcd_nonzero a g1
  have g2: 0 < b := by linarith
  have h2 : a / b = 0 := by
    rw [Nat.div_eq_zero_iff_lt g2]
    apply h
    done
  have h3 : b * (a / b) + a % b = a := Nat.div_add_mod a b
  rw[h2, mul_zero, zero_add] at h3
  rw [h3] at h1
  apply h1
  done

theorem gcd_comm (a b : Nat) : gcd a b = gcd b a := by
  by_cases h1: a < b
  · -- a < b
    apply gcd_comm_lt h1
  · by_cases h2: a = b
    · -- a = b
      rw [h2]
    · -- a > b
      have h3 := by apply Nat.lt_or_gt_of_ne h2
      disj_syll h3 h1
      have h4 : b < a := by linarith
      have h := by apply gcd_comm_lt h4
      symm
      apply h
    done

-- 3.
theorem Exercise_7_1_5 (a b : Nat) (n : Int) :
    (∃ (s t : Int), s * a + t * b = n) ↔ (↑(gcd a b) : Int) ∣ n := by
    apply Iff.intro
    · -- (->)
      intros h1
      obtain s tmp from h1; clear h1
      obtain t h1 from tmp; clear tmp
      have h2 := by apply gcd_dvd_left a b
      define at h2; obtain k1 hk1 from h2; clear h2
      have h3 := by apply gcd_dvd_right a b
      define at h3; obtain k2 hk2 from h3; clear h3
      rw [hk1] at h1
      nth_rewrite 2 [hk2] at h1
      define
      exists s * k1 + t * k2
      rw [← h1]; ring
      rw [mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_mul]
      done
    · -- (<-)
      intros h1; define at h1
      obtain k hk from h1; clear h1
      have h2 := by apply gcd_lin_comb b a
      rw [← h2] at hk
      exists (gcd_c1 a b) * k
      exists (gcd_c2 a b) * k
      rw [hk]
      ring
    done

-- 4.
theorem Exercise_7_1_6 (a b c : Nat) :
    gcd a b = gcd (a + b * c) b := by
    by_cases h: b = 0
    · --b = 0
      rw [h]; ring
    · --b ≠ 0
      have h1: (a + b * c) % b = a % b := by
        set r := a % b
        have g1 : b * (a / b) + r = a := Nat.div_add_mod a b
        rw [Nat.mod_eq_iff]; apply Or.inr
        apply And.intro
        · apply mod_nonzero_lt; apply h
        · exists (a / b + c)
          nth_rewrite 1 [← g1]
          ring
        done
      have h2 := by apply gcd_nonzero (a + b * c) h
      rw[h1] at h2
      have h3 := by apply gcd_nonzero a h
      rw [h2, h3]
      done

-- 5.
theorem gcd_is_nonzero {a b : Nat} (h : a ≠ 0 ∨ b ≠ 0) :
    gcd a b ≠ 0 := by
    by_cases on h
    · -- a ≠ 0
      have h1 := by apply gcd_dvd_left a b
      define at h1; obtain k h2 from h1; clear h1
      contradict h with h1
      rw [h2, h1]
      ring
    · --b ≠ 0
      have h1 := by apply gcd_dvd_right a b
      define at h1; obtain k h2 from h1; clear h1
      contradict h with h1
      rw [h2, h1]
      ring
    done

-- 6.
theorem gcd_greatest {a b d : Nat} (h1 : gcd a b ≠ 0)
    (h2 : d ∣ a) (h3 : d ∣ b) : d ≤ gcd a b := by
    have h := by apply Theorem_7_1_6 h2 h3
    define at h; obtain k hk from h; clear h
    rw[hk] at h1
    rw [Nat.mul_ne_zero_iff] at h1
    have h4 := h1.right
    rw [Nat.ne_zero_iff_zero_lt] at h4
    have h5 : 1 ≤ k := by linarith
    rw[hk]
    have g1 : d = d * 1 := by ring
    nth_rw 1 [g1]
    apply Nat.mul_le_mul_left d h5
    done

-- 7.
lemma Lemma_7_1_10a {a b : Nat}
    (n : Nat) (h : a ∣ b) : (n * a) ∣ (n * b) := by
    define at h; obtain k hk from h; clear h
    define; exists k
    rw [hk]; ring
    done

lemma Lemma_7_1_10b {a b n : Nat}
    (h1 : n ≠ 0) (h2 : (n * a) ∣ (n * b)) : a ∣ b := by
    define at h2; obtain k h3 from h2; clear h2
    define; exists k
    #check Nat.mul_left_cancel
    #check Nat.pos_of_ne_zero
    have g: 0 < n := by apply Nat.pos_of_ne_zero h1
    rw [mul_assoc] at h3
    apply Nat.mul_left_cancel g h3
    done

lemma Lemma_7_1_10c {a b : Nat}
    (h1 : a ∣ b) (h2 : b ∣ a) : a = b := by
    by_cases h: b = 0
    · --b = 0
      define at h1
      obtain k h3 from h2; clear h2
      rw [h3, h]
      ring
    · --b ≠ 0
      define at h1; obtain x g1 from h1; clear h1
      define at h2; obtain y g2 from h2; clear h2
      have h1 := g1
      rw [g2] at h1
      have h2 : b = b * 1 := by ring
      nth_rw 1 [h2] at h1; clear h2
      rw [mul_assoc] at h1
      have g3 : 0 < b := by apply Nat.pos_of_ne_zero h
      apply Nat.mul_left_cancel g3 at h1
      symm at h1
      apply Nat.eq_one_of_mul_eq_one_right at h1
      rw [h1] at g2
      rw [g2]; ring
    done

theorem Exercise_7_1_10 (a b n : Nat) :
    gcd (n * a) (n * b) = n * gcd a b := by
    apply Lemma_7_1_10c
    · --gcd (n * a) (n * b) ∣ n * gcd a b
      have h1 := by apply gcd_dvd_left (n * a) (n * b)
      have h2 := by apply gcd_dvd_right (n * a) (n * b)
      obtain k1 hna from h1; clear h1
      obtain k2 hnb from h2; clear h2
      have h:= by apply gcd_lin_comb b a
      rw [← Int.natCast_dvd_natCast]
      define
      exists (gcd_c1 a b) * k1 + (gcd_c2 a b) * k2
      show ↑(n * gcd a b) = ↑(gcd (n * a) (n * b)) * (gcd_c1 a b * ↑k1 + gcd_c2 a b * ↑k2) from
        calc ↑(n * gcd a b)
          _ = ↑n * ↑(gcd a b) := by rw[Nat.cast_mul]
          _ = ↑n * (gcd_c1 a b * ↑a + gcd_c2 a b * ↑b) := by rw [h]
          _ = ↑n * gcd_c1 a b * ↑a + ↑n * gcd_c2 a b * ↑b := by rw[left_distrib, mul_assoc, mul_assoc]
          _ = ↑(n * a) * gcd_c1 a b + ↑(n * b) * gcd_c2 a b := by
            rw[mul_right_comm]; nth_rewrite 2 [mul_right_comm]; rw [← Nat.cast_mul, ← Nat.cast_mul]
          _ = ↑(gcd (n * a) (n * b) * k1) * gcd_c1 a b + ↑(gcd (n * a) (n * b) * k2) * gcd_c2 a b := by nth_rewrite 1 [hna]; nth_rewrite 2 [hnb]; rfl
          _ = ↑(gcd (n * a) (n * b)) * (gcd_c1 a b * ↑k1 + gcd_c2 a b * ↑k2) := by rw [Nat.cast_mul, mul_assoc, Nat.cast_mul, mul_assoc, left_distrib]; rw [mul_comm ↑k1 (gcd_c1 a b), mul_comm ↑k2 (gcd_c2 a b)]
      done
      --na = k1 * gcd(na, nb)
      --nb = k2 * gcd(na, nb)
      --gcd_c1(a, b)*na + gcd_c2(a, b) * nb = n * gcd (a, b)
      --(gcd_c1(a, b) * k1 + gcd_c2(a, b) * k2) * gcd(na, nb) = n * gcd(a, b)

    · --n * gcd a b | gcd (n * a) (n * b)
      have h1 := by apply gcd_dvd_left a b
      have h2 := by apply gcd_dvd_right a b
      obtain k1 ha from h1
      obtain k2 hb from h2
      have h:= by apply gcd_lin_comb (n * b) (n * a)
      rw [← Int.natCast_dvd_natCast]
      define
      exists (gcd_c1 (n * a) (n * b) * k1 + gcd_c2 (n * a) ( n * b) * k2)
      show ↑(gcd (n * a) (n * b)) = ↑(n * gcd a b) * (gcd_c1 (n * a) (n * b) * ↑k1 + gcd_c2 (n * a) (n * b) * ↑k2) from
        calc ↑(gcd (n * a) (n * b))
          _ = gcd_c1 (n * a) (n * b) * ↑(n * a) + gcd_c2 (n * a) (n * b) * ↑(n * b) := by rw [h]
          _ = gcd_c1 (n * a) (n * b) * ↑(n * (gcd a b * k1)) + gcd_c2 (n * a) (n * b) * ↑(n * (gcd a b * k2)) := by nth_rewrite 2 [ha]; nth_rewrite 4 [hb]; rfl
          _ = gcd_c1 (n * a) (n * b) * ↑(n * gcd a b) * ↑k1 + gcd_c2 (n * a) (n * b) * ↑(n * gcd a b) * ↑k2 := by ring; rw [Nat.cast_mul]; nth_rewrite 2 [Nat.cast_mul]; rw[←mul_assoc, ←mul_assoc]
          _ = ↑(n * gcd a b) * gcd_c1 (n * a) (n * b) * ↑k1 + ↑(n * gcd a b) * gcd_c2 (n * a) (n * b) * ↑k2 := by nth_rw 2 [mul_comm]; rw [mul_comm (gcd_c2 (n * a) (n * b)) ↑(n * gcd a b)]
          _ = ↑(n * gcd a b) * (gcd_c1 (n * a) (n * b) * ↑k1 + gcd_c2 (n * a) (n * b) * ↑k2) := by rw[left_distrib, mul_assoc, mul_assoc]
      done
      -- a = k1 * gcd(a, b)
      -- b = k2 * gcd(a, b)
      -- gcd(na, nb) = gcd_c1(na, nb) * n * a + gcd_c2(na, nb) * n * b
      --             = (gcd_c1(na, nb)* k1 + gcd_c2(na,nb) * k2) * n * gcd(a, b)

/- Section 7.2 -/
-- 1.
lemma dvd_prime {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := sorry

-- 2.
-- Hints:  Start with apply List.rec.  You may find mul_ne_zero useful
theorem prod_nonzero_nonzero : ∀ (l : List Nat),
    (∀ a ∈ l, a ≠ 0) → prod l ≠ 0 := sorry

-- 3.
theorem rel_prime_iff_no_common_factor (a b : Nat) :
    rel_prime a b ↔ ¬∃ (p : Nat), prime p ∧ p ∣ a ∧ p ∣ b := sorry

-- 4.
theorem rel_prime_symm {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := sorry

-- 5.
lemma in_prime_factorization_iff_prime_factor {a : Nat} {l : List Nat}
    (h1 : prime_factorization a l) (p : Nat) :
    p ∈ l ↔ prime_factor p a := sorry

-- 6.
theorem Exercise_7_2_5 {a b : Nat} {l m : List Nat}
    (h1 : prime_factorization a l) (h2 : prime_factorization b m) :
    rel_prime a b ↔ (¬∃ (p : Nat), p ∈ l ∧ p ∈ m) := sorry

-- 7.
theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry

-- 8.
theorem Exercise_7_2_7 {a b a' b' : Nat}
    (h1 : rel_prime a b) (h2 : a' ∣ a) (h3 : b' ∣ b) :
    rel_prime a' b' := sorry

-- 9.
theorem Exercise_7_2_9 {a b j k : Nat}
    (h1 : gcd a b ≠ 0) (h2 : a = j * gcd a b) (h3 : b = k * gcd a b) :
    rel_prime j k := sorry

-- 10.
theorem Exercise_7_2_17a (a b c : Nat) :
    gcd a (b * c) ∣ gcd a b * gcd a c := sorry

/- Section 7.3 -/
-- 1.
theorem congr_trans {m : Nat} : ∀ {a b c : Int},
    a ≡ b (MOD m) → b ≡ c (MOD m) → a ≡ c (MOD m) := sorry

-- 2.
theorem Theorem_7_3_6_3 {m : Nat} (X : ZMod m) : X + [0]_m = X := sorry

-- 3.
theorem Theorem_7_3_6_4 {m : Nat} (X : ZMod m) :
    ∃ (Y : ZMod m), X + Y = [0]_m := sorry

-- 4.
theorem Exercise_7_3_4a {m : Nat} (Z1 Z2 : ZMod m)
    (h1 : ∀ (X : ZMod m), X + Z1 = X)
    (h2 : ∀ (X : ZMod m), X + Z2 = X) : Z1 = Z2 := sorry

-- 5.
theorem Exercise_7_3_4b {m : Nat} (X Y1 Y2 : ZMod m)
    (h1 : X + Y1 = [0]_m) (h2 : X + Y2 = [0]_m) : Y1 = Y2 := sorry

-- 6.
theorem Theorem_7_3_10 (m a : Nat) (b : Int) :
    ¬(↑(gcd m a) : Int) ∣ b → ¬∃ (x : Int), a * x ≡ b (MOD m) := sorry

-- 7.
theorem Theorem_7_3_11 (m n : Nat) (a b : Int) (h1 : n ≠ 0) :
    n * a ≡ n * b (MOD n * m) ↔ a ≡ b (MOD m) := sorry

-- 8.
theorem Exercise_7_3_16 {m : Nat} {a b : Int} (h : a ≡ b (MOD m)) :
    ∀ (n : Nat), a ^ n ≡ b ^ n (MOD m) := sorry

-- 9.
example {m : Nat} [NeZero m] (X : ZMod m) :
    ∃! (a : Int), 0 ≤ a ∧ a < m ∧ X = [a]_m := sorry

-- 10.
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := sorry

-- 11.
--Hint: You may find the theorem Int.ofNat_mod_ofNat useful.
theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := sorry

-- 12.
lemma congr_iff_mod_eq_Int (m : Nat) (a b : Int) [NeZero m] :
    a ≡ b (MOD m) ↔ a % ↑m = b % ↑m := sorry

--Hint for next theorem: Use the lemma above,
--together with the theorems Int.ofNat_mod_ofNat and Nat.cast_inj.
theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := sorry

/- Section 7.4 -/
-- 1.
--Hint:  Use induction.
--For the base case, compute [a]_m ^ 0 * [1]_m in two ways:
--by Theorem_7_3_6_7, [a] ^ 0 * [1]_m = [a]_m ^ 0
--by ring, [a]_m ^ 0 * [1]_m = [1]_m.
lemma Exercise_7_4_5_Int (m : Nat) (a : Int) :
    ∀ (n : Nat), [a]_m ^ n = [a ^ n]_m := sorry

-- 2.
lemma left_inv_one_one_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := sorry

-- 3.
lemma comp_perm_below {n : Nat} {f g : Nat → Nat}
    (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := sorry

-- 4.
lemma perm_below_fixed {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := sorry

-- 5.
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

-- 6.
example {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    a ^ (phi m + 1) ≡ a (MOD m) := sorry

-- 7.
theorem Like_Exercise_7_4_11 {m a p : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p + 1 = phi m) :
    [a]_m * [a ^ p]_m = [1]_m := sorry

-- 8.
theorem Like_Exercise_7_4_12 {m a p q k : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p = q + (phi m) * k) :
    a ^ p ≡ a ^ q (MOD m) := sorry

/- Section 7.5 -/
-- 1.
--Hint:  Use induction.
lemma num_rp_prime {p : Nat} (h1 : prime p) :
    ∀ k < p, num_rp_below p (k + 1) = k := sorry

-- 2.
lemma three_prime : prime 3 := sorry

-- 3.
--Hint:  Use the previous exercise, Exercise_7_2_7, and Theorem_7_4_2.
theorem Exercise_7_5_13a (a : Nat) (h1 : rel_prime 561 a) :
    a ^ 560 ≡ 1 (MOD 3) := sorry

-- 4.
--Hint:  Imitate the way Theorem_7_2_2_Int was proven from Theorem_7_2_2.
lemma Theorem_7_2_3_Int {p : Nat} {a b : Int}
    (h1 : prime p) (h2 : ↑p ∣ a * b) : ↑p ∣ a ∨ ↑p ∣ b := sorry

-- 5.
--Hint:  Use the previous exercise.
theorem Exercise_7_5_14b (n : Nat) (b : Int)
    (h1 : prime n) (h2 : b ^ 2 ≡ 1 (MOD n)) :
    b ≡ 1 (MOD n) ∨ b ≡ -1 (MOD n) := sorry
