#![feature(iterator_try_collect)]
use num_rational::Ratio;
use std::ops::{Add, Neg, Sub, Mul, Div};
use std::fmt;

#[derive(Debug, Clone, Eq)]
struct Mono(Vec<usize>, usize); // Prod_i x^a_i, vec.len()
impl Mono {
    fn new(indets: Vec<usize>) -> Self {
        let n = indets.len();
        Mono(indets, n)
    }

    fn extend(self, n: usize) -> Self {
        if n < self.1 {
            panic!();
        }

        let mut indets = self.0;
        indets.resize(n, 0);
        Mono(indets, n)
    }

    fn lcm(self, other: Self) -> Self {
        let mut n = self.1;
        let mut lhs_vec = self.0;
        let mut rhs_vec = other.0;
        if self.1 > other.1 {
            rhs_vec.resize(n, 0);
        }
        if other.1 > self.1 {
            n = other.1;
            lhs_vec.resize(n, 0);
        }

        Mono(lhs_vec.into_iter()
            .zip(rhs_vec.into_iter())
            .map(|(a, b)| std::cmp::max(a, b))
            .collect(), n)
    }

    fn div(self, other: Self) -> Option<Self> {
        let mut n = self.1;
        let mut lhs_vec = self.0;
        let mut rhs_vec = other.0;
        if self.1 > other.1 {
            rhs_vec.resize(n, 0);
        }
        if other.1 > self.1 {
            n = other.1;
            lhs_vec.resize(n, 0);
        }

        lhs_vec.into_iter()
            .zip(rhs_vec.into_iter())
            .map(|(a, b)| a.checked_sub(b))
            .try_collect()
            .map(|x| Mono(x, n))
    }

    fn is_none(&self) -> bool {
        self.0.iter().all(|x| *x == 0)
    }
}

impl PartialEq for Mono {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Mul for Mono {
    type Output = Mono;

    fn mul(self, other: Self) -> Self::Output {
        let mut n = self.1;
        let mut lhs_vec = self.0;
        let mut rhs_vec = other.0;
        if self.1 > other.1 {
            rhs_vec.resize(n, 0);
        }
        if other.1 > self.1 {
            n = other.1;
            lhs_vec.resize(n, 0);
        }

        Mono(lhs_vec
        .into_iter()
        .zip(rhs_vec.into_iter())
        .map(|(x, y)| x + y)
        .collect(), n)
    }
}

impl fmt::Display for Mono {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.1 < 27 {
            let alphabet = "xyzwabcdefghijklmnopqrstuv".as_bytes();
            for (x, a) in (0..self.1).zip(self.0.iter()) {
                if *a > 0 {
                    if *a == 1 {
                        write!(f, "{}", alphabet[x] as char)?;
                    } else {
                        write!(f, "{}^{}", alphabet[x] as char, a)?;
                    }
                }
            }
        } else {
            for (x, a) in (0..self.1).zip(self.0.iter()) {
                if *a > 0 {
                    if *a == 1 {
                        write!(f, "x{}", x)?;
                    } else {
                        write!(f, "x{}^{}", x, a)?;
                    }
                }
            }
        }
        fmt::Result::Ok(())
    }
}

#[derive(Eq, PartialEq, Copy, Clone)]
enum MonoOrdT {
    Lex,
    DegLex,
}
use MonoOrdT::*;
impl Mono {
    fn compare(&self, other: &Self, ty: MonoOrdT) -> std::cmp::Ordering {
        match ty {
            Lex => {
                let mut lhs_vec = self.0.clone();
                let mut rhs_vec = other.0.clone();
                if self.1 > other.1 {
                    rhs_vec.resize(self.1, 0);
                } else if self.1 < other.1 {
                    lhs_vec.resize(other.1, 0);
                }

                for (a, b) in lhs_vec.into_iter().zip(rhs_vec.into_iter()) {
                    if a > b {
                        return std::cmp::Ordering::Greater
                    } else if a < b {
                        return std::cmp::Ordering::Less
                    }
                }
                std::cmp::Ordering::Equal
            },
            DegLex => {
                let lhs_deg: usize = self.0.iter().sum();
                let rhs_deg: usize = other.0.iter().sum();
                if lhs_deg > rhs_deg {
                    std::cmp::Ordering::Greater
                } else if lhs_deg < rhs_deg {
                    std::cmp::Ordering::Less
                } else {
                    self.compare(other, Lex)
                }
            }
        }
    }
}

type K = Ratio<i32>;
type Term = (K, Mono);
#[derive(Debug, Clone)]
struct Poly(Vec<Term>, usize); // Sum_j c_j * (Prod_i x^a_i)
impl Poly {
    fn new(monos: Vec<Term>) -> Self {
        let mut seq = monos.iter();
        let mut k = 0;

        if let Some((_, Mono(_, n))) = seq.next() {
            if !seq.all(|(_, Mono(_, m))| m == n) {
                panic!()
            }
            k = *n;
        }

        Poly(monos, k)
    }

    fn lt(&mut self, ty: MonoOrdT) -> Term {
        self.0.sort_by(|(_, m0), (_, m1)| m0.compare(m1, ty).reverse());
        self.0[0].clone()
    }

    fn lm(&mut self, ty: MonoOrdT) -> Mono {
        self.lt(ty).1
    }

    fn spoly(mut self, mut other: Self, ty: MonoOrdT) -> Self {
        let ((c0, m0), (c1, m1)) = (self.lt(ty), other.lt(ty));
        let L = m0.clone().lcm(m1.clone());
        let d0 = (Ratio::new(1, 1) / c0);
        let d1 = (Ratio::new(1, 1) / c1);

        self * (d0, L.clone().div(m0).unwrap()) - other * (d1, L.div(m1).unwrap())
    }

    fn univariate(&self) -> Option<usize> {
        let mut seq = self.0.iter();
        match seq.next() {
            Some((_, Mono(indets, _))) => {
                let mut non_zeros = indets
                .iter()
                .zip(0..indets.len())
                .filter(|(a, _)| **a != 0);

                match non_zeros.next() {
                    Some((_, i0)) => {
                        if non_zeros.next().is_some() {
                            return None
                        }

                        if seq.all(|(_, Mono(indets, _))| {
                            indets
                            .iter()
                            .zip(0..indets.len())
                            .all(|(a, i)| if i != i0 { *a == 0 } else { true })
                        }) { Some(i0) } else { None }
                    },
                    None => None,
                }
            }
            None => None,
        }
    }
}

impl Add for Poly {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut n = self.1;
        let mut lhs_vec = self.0;
        let mut rhs_vec = rhs.0;

        if self.1 > rhs.1 {
            rhs_vec = rhs_vec
            .into_iter()
            .map(|(c, x)| (c, x.extend(n)))
            .collect();
        }
        if self.1 < rhs.1 {
            n = rhs.1;
            lhs_vec = lhs_vec
            .into_iter()
            .map(|(c, x)| (c, x.extend(n)))
            .collect();
        }

        let mut res = Vec::new();
        for (c0, x0) in lhs_vec {
            if let Some(i) = rhs_vec.iter().position(|(_, x1)| x0 == *x1) {
                let (c1, x1) = rhs_vec.remove(i);
                res.push((c0 + c1, x1));
            } else {
                res.push((c0, x0));
            }
        }
        res.append(&mut rhs_vec);
        res.retain(|(c, _)| *c != 0.into());
        Poly(res, n)
    }
}

impl Neg for Poly {
    type Output = Poly;

    fn neg(self) -> Self::Output {
        Poly(self.0.into_iter().map(|(c, x)| (-c, x)).collect(), self.1)
    }
}

impl Sub for Poly {
    type Output = Poly;

    fn sub(self, rhs: Self) -> Self::Output {
        self + -rhs
    }
}

impl Mul<Term> for Poly {
    type Output = Poly;

    fn mul(self, rhs: Term) -> Self::Output {
        let (c0, x0) = rhs;
        let n = std::cmp::max(self.1, x0.1);
        Poly(self.0
        .into_iter()
        .map(|(c, x)| (c * c0, x * x0.clone()))
        .collect(), n)
    }
}

impl Mul for Poly {
    type Output = Poly;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut seq = rhs.0.into_iter();
        match seq.next() {
            Some(tm) => {
                let acc = self.clone() * tm;
                seq.fold(acc, |acc, tm| {
                    acc + self.clone() * tm
                })
            }
            None => panic!(),
        }
    }
}

impl Div<Vec<Poly>> for Poly {
    type Output = (Vec<Poly>, Poly);

    fn div(self, ideal: Vec<Poly>) -> Self::Output {
        let mut f = self;
        let mut quot = Vec::new();
        quot.resize(ideal.len(), Poly::new(vec![]));
        let mut rem = Poly::new(vec![]);

        while !f.0.is_empty() {
            let (c_f, m_f) = f.lt(DegLex);
            let mut break_ = false;
            for (g, i) in ideal.iter().zip(0..ideal.len()) {
                let (c_g, m_g) = g.clone().lt(DegLex);
                if let Some(q) = m_f.clone().div(m_g) {
                    quot[i] = quot[i].clone() + Poly::new(vec![(c_f / c_g, q.clone())]);
                    f = f - g.clone() * (c_f / c_g, q);
                    break_ = true;
                    break
                }
            }
            if !break_ {
                rem = rem + Poly::new(vec![(c_f, m_f)]);
                f.0.remove(0);
            }
        }

        (quot, rem)
    }
}

impl fmt::Display for Poly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (c, x) = &self.0[0];
        if *c == 1.into() && !x.is_none() {
            write!(f, "{}", x)?;
        } else {
            write!(f, "{}{}", c, x)?;
        }

        if self.0.len() > 1 {
            if self.0[1].0 > 0.into() {
                write!(f, " + ")?;
            } else {
                write!(f, " - ")?;
            }

            for i in 1..self.0.len() - 1 {
                let (c, x) = &self.0[i];
                if (*c == 1.into() || *c == (-1).into()) && !x.is_none() {
                    write!(f, "{}", x)?;
                } else {
                    write!(f, "{}{}", Ratio::new(c.numer().abs(), *c.denom()), x)?;
                }

                if self.0[i + 1].0 > 0.into() {
                    write!(f, " + ")?;
                } else {
                    write!(f, " - ")?;
                }
            }
            let (c, x) = &self.0[self.0.len() - 1];
            if (*c == 1.into() || *c == (-1).into()) && !x.is_none() {
                write!(f, "{}", x)?;
            } else {
                write!(f, "{}{}", Ratio::new(c.numer().abs(), *c.denom()), x)?;
            }
        }
        fmt::Result::Ok(())
    }
}

fn buchberger(basis: Vec<Poly>) -> Vec<Poly> {
    let mut res = basis.clone();
    let mut r = bruteforce(basis);
    while !r.is_empty() {
        res.append(&mut r);
        r = bruteforce(res.clone());
    }
    res
}

fn bruteforce(basis: Vec<Poly>) -> Vec<Poly> {
    let mut res: Vec<Poly> = Vec::new();
    for i in 0..basis.len() {
        for j in 0..basis.len() {
            let (_, r) = basis[i].clone().spoly(basis[j].clone(), DegLex) / basis.clone();
            if !r.0.is_empty() {
                res.push(r);
            }
        }
    }
    res
}

fn main() {
    let p = Poly::new(vec![
        (1.into(), Mono::new(vec![2, 1])),
        (1.into(), Mono::new(vec![1, 2])),
        (1.into(), Mono::new(vec![0, 2]))]);
    let q1 = Poly::new(vec![
        (1.into(), Mono::new(vec![0, 2])),
        ((-1).into(), Mono::new(vec![0, 0]))
    ]);
    let q2 = Poly::new(vec![
        (1.into(), Mono::new(vec![1, 1])),
        ((-1).into(), Mono::new(vec![0, 0]))
    ]);

    println!("p = {}\nq1 = {}\nq2 = {}", p.clone(), q1.clone(), q2.clone());
    let (h, r) = p / vec![q1, q2];
    println!("p / <q1, q2> = [");
    for hs in h {
        println!("{}", hs);
    }
    println!("],");
    println!("{}", r);

    let p1 = Poly::new(vec![
    (2.into(), Mono::new(vec![2, 0])),
    ((-4).into(), Mono::new(vec![1, 0])),
    (1.into(), Mono::new(vec![0, 2])),
    ((-4).into(), Mono::new(vec![0, 1])),
    (3.into(), Mono::new(vec![0, 0]))
    ]);
    let p2 = Poly::new(vec![
    (1.into(), Mono::new(vec![2, 0])),
    ((-2).into(), Mono::new(vec![1, 0])),
    (3.into(), Mono::new(vec![0, 2])),
    ((-12).into(), Mono::new(vec![0, 1])),
    (9.into(), Mono::new(vec![0, 0]))
    ]);

    println!("p1 = {}\np2 = {}", p1.clone(), p2.clone());
    let res = buchberger(vec![p1, p2]);
    println!("The Groebner basis of <p1, p2> = [");
    for hs in res.clone() {
        println!("{}", hs);
    }
    println!("]");
}
