# Verified Modular Arithmetic

A formal verification project in Lean 4 that develops the foundations of modular arithmetic and congruence relations.

This project was created as a learning exercise in theorem proving and formal verification using Lean 4 and Mathlib. The goal is to verify basic properties of modular arithmetic that are widely used in number theory, cryptography, and computer science.

---

## Motivation

Modular arithmetic is a fundamental component of modern cryptography.

Many cryptographic algorithms, including RSA, Diffie-Hellman, and Elliptic Curve Cryptography, rely on arithmetic performed modulo an integer.

Rather than testing algorithms with examples, formal verification proves mathematically that properties always hold.

This project demonstrates how Lean 4 can be used to formally verify such properties.

---

## Definitions

The project defines:

### Modular Addition

```lean
def modAdd (a b n : Nat) : Nat :=
  (a + b) % n
```

### Congruence Modulo n

```lean
def congruentMod (a b n : Nat) : Prop :=
  (a % n) = (b % n)
```

Two numbers are congruent modulo `n` when they have the same remainder upon division by `n`.

---

## Verified Properties

### Modular Addition

The following properties were formally proved:

- Commutativity
- Associativity
- Identity element (zero)

Examples:

```text
(a + b) mod n = (b + a) mod n
```

```text
((a + b) mod n + c) mod n
=
(a + (b + c) mod n) mod n
```

---

### Congruence Relation

The project proves that congruence modulo `n` forms an equivalence relation.

#### Reflexive

```text
a ≡ a (mod n)
```

#### Symmetric

```text
a ≡ b (mod n)
⇒
b ≡ a (mod n)
```

#### Transitive

```text
a ≡ b (mod n)
b ≡ c (mod n)
⇒
a ≡ c (mod n)
```

---

### Compatibility properties

The project proves that congruence is preserved under arithmetic operations.

#### Addition

```text
a ≡ b (mod n)
c ≡ d (mod n)

⇒

a + c ≡ b + d (mod n)
```

#### Multiplication

```text
a ≡ b (mod n)
c ≡ d (mod n)

⇒

ac ≡ bd (mod n)
```

#### Adding the Same Constant

```text
a ≡ b (mod n)

⇒

a + c ≡ b + c (mod n)
```

#### Multiplying by the Same Constant

```text
a ≡ b (mod n)

⇒

ac ≡ bc (mod n)
```

---

### Additional Results

The project also verifies several useful modular arithmetic identities:

```text
(a mod n) mod n = a mod n
```

```text
0 mod n = 0
```

```text
n mod n = 0
```

```text
((a mod n) + (b mod n)) mod n
=
(a + b) mod n
```

```text
((a mod n) × (b mod n)) mod n
=
(a × b) mod n
```

---

### Greatest Common Divisor

The project includes verified properties of the greatest common divisor:

#### Commutativity

```text
gcd(a,b) = gcd(b,a)
```

#### Self Property

```text
gcd(a,a) = a
```

#### gcd(a,1)

```text
gcd(a,1) = 1
```

These properties are important in number theory and cryptographic applications involving coprimality.


---

## Learning Outcomes

This project demonstrates:

- Formal theorem proving
- Mathematical verification
- Modular arithmetic
- Congruence relations
- Number theoretic reasoning
- Use of Lean tactics such as:

```text
rw
simp
exact
apply
unfold
rfl
```

---

## Future Work

Possible extensions include:

- Modular exponentiation
- Euclidean Algorithm
- Extended Euclidean Algorithm
- Coprimality proofs
- Modular inverses
- RSA-related formalizations
- Fermat's Little Theorem
- Euler's Theorem

---

## Author

Shridhar Naik

Independent Lean 4 formal verification project.