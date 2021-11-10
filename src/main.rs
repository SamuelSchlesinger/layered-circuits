use bitvec::vec::BitVec;
use bitvec::{bitvec};
use bitvec::order::{LocalBits};
use std::collections::BTreeMap;

/// The type of a gate within a circuit
#[derive(Debug)]
enum GateType {
    AND,
    OR,
}

impl GateType {
    fn compute(&self, x: bool, y: bool) -> bool {
        match self {
            GateType::AND => x & y,
            GateType::OR => x | y,
        }
    }
}

/// A literal circuit input, either negated or not
#[derive(Debug)]
enum Lit<T> {
    Not(T),
    NotNot(T),
}

struct LitIter {
    input_size: usize,
    lit: Lit<usize>,
    finished: bool,
}

impl Iterator for LitIter {
    type Item = Lit<usize>;
    fn next(self: &mut LitIter) -> Option<Lit<usize>> {
        if !self.finished {
            match self.lit {
                Lit::NotNot(t) => {
                    self.lit = Lit::Not(t);
                    Some(Lit::Not(t))
                },
                Lit::Not(t) => {
                    if t >= self.input_size {
                        self.finished = true;
                        None
                    } else {
                        self.lit = Lit::NotNot(t + 1);
                        Some(Lit::NotNot(t + 1))
                    }
                },
            }
        } else {
            None
        }
    }
}


impl<T> Lit<T> {
    /// Sometimes we just want to know which input we're looking at,
    /// not what its sign is
    fn unliteral(&self) -> &T {
        match self {
            Lit::Not(t) => t,
            Lit::NotNot(t) => t,
        }
    }

    /// Is this literal negated?
    fn negated(&self) -> bool {
        match self {
            Lit::Not(_) => true,
            Lit::NotNot(_) => false,
        }
    }

    fn enumerate(input_size: usize) -> LitIter {
        LitIter {
            input_size,
            lit: Lit::NotNot(0),
            finished: false,
        }
    }
}

/// A single gate in a layer
#[derive(Debug)]
struct Gate {
    gate_type: GateType,
    gate_inputs: (Lit<usize>, Lit<usize>),
}

impl Gate {
    fn and(li: Lit<usize>, lj: Lit<usize>) -> Gate {
        Gate {
            gate_type: GateType::AND,
            gate_inputs: (li, lj),
        }
    }

    fn or(li: Lit<usize>, lj: Lit<usize>) -> Gate {
        Gate {
            gate_type: GateType::OR,
            gate_inputs: (li, lj),
        }
    }
}

/// A layer of gates
#[derive(Debug)]
struct Layer {
    gates: Vec<Gate>,
}

impl Layer {
    fn width(&self) -> usize {
        self.gates.len()
    }

    fn push_gate(&mut self, gate: Gate) {
        self.gates.push(gate);
    }

    fn pop_gate(&mut self) {
        self.gates.pop();
    }

    fn execute(&self, input: &BitVec) -> BitVec {
        let mut output = BitVec::new();
        for g in &self.gates {
            output.push(g.gate_type.compute(
                g.gate_inputs.0.negated() ^ input[*g.gate_inputs.0.unliteral()],
                g.gate_inputs.1.negated() ^ input[*g.gate_inputs.1.unliteral()],
            ));
        }
        output
    }

    fn new(gates: Vec<Gate>) -> Layer {
        Layer { gates }
    }
}

/// An entire circuit
#[derive(Debug)]
struct Circuit {
    input_size: usize,
    layers: Vec<Layer>,
}

impl Circuit {
    fn input_size(&self) -> usize {
        self.input_size
    }

    fn output_size(&self) -> usize {
        self.layers[self.layers.len() - 1].width()
    }

    fn execute(&self, input: &BitVec) -> BitVec {
        if input.len() == self.input_size {
            if self.layers.len() == 0 {
                input.clone()
            } else {
                let mut state = self.layers[0].execute(input);
                for v in &self.layers[1..] {
                    state = v.execute(&state);
                }
                state
            }
        } else {
            panic!("bad input size to Circuit.execute()")
        }
    }
}

struct BooleanFn {
    input_size: usize,
    output_size: usize,
    function: fn(&BitVec) -> BitVec,
}

impl BooleanFn {
    fn execute(&self, input: &BitVec) -> BitVec {
        (self.function)(input)
    }

    fn xor(n: usize) -> Self {
        BooleanFn {
            input_size: n,
            output_size: 1,
            function: |v| {
                let mut bv = BitVec::new();
                bv.push(v.iter().fold(false, |x, b| { x ^ *b }));
                bv
            }
        }
    }
}

struct CachedCircuit {
    circuit: Circuit,
    cache: BTreeMap<BitVec, Vec<BitVec>>,
}

impl Circuit {
    fn push_layer(&mut self, layer: Layer) {
        self.layers.push(layer);
    }

    fn cached(self) -> CachedCircuit {
        CachedCircuit {
            circuit: self,
            cache: BTreeMap::new(),
        }
    }

    fn new(n: usize) -> Circuit {
        Circuit {
            input_size: n,
            layers: Vec::new(),
        }
    }

    fn xor(n: usize) -> Circuit {
        let mut circuit = Circuit::new(n);
        let mut m = n;
        while m != 1 {
            if m % 2 == 0 {
                let and_layer = Layer::new((0..m/2).into_iter().flat_map(|i| {
                    vec![Gate::and(Lit::Not(2 * i), Lit::NotNot(2*i + 1)), Gate::and(Lit::NotNot(2 * i), Lit::Not(2*i + 1))]
                }
                ).collect::<Vec<Gate>>());
                circuit.push_layer(and_layer);
                let or_layer = Layer::new((0..m/2).into_iter().map(|i| {
                    Gate::or(Lit::NotNot(2 * i), Lit::NotNot(2 * i + 1))
                }).collect::<Vec<Gate>>());
                circuit.push_layer(or_layer);
                m /= 2;
            } else {
                let mut first_layer = Layer::new((0..m - 2).into_iter().map(|i| {
                    Gate::and(Lit::NotNot(i), Lit::NotNot(i))
                }).collect::<Vec<Gate>>());
                first_layer.push_gate(Gate::and(Lit::Not(m - 2), Lit::NotNot(m - 1)));
                first_layer.push_gate(Gate::and(Lit::NotNot(m - 2), Lit::Not(m - 1)));
                circuit.push_layer(first_layer);
                let mut second_layer = Layer::new((0..m - 2).into_iter().map(|i| {
                    Gate::and(Lit::NotNot(i), Lit::NotNot(i))
                }).collect::<Vec<Gate>>());
                second_layer.push_gate(Gate::or(Lit::NotNot(m - 1), Lit::NotNot(m - 2)));
                circuit.push_layer(second_layer);
                m -= 1;
            }
        }
        circuit
    }
}

struct BinaryStrings {
    length: usize,
    finished: bool,
    current: BitVec,
}

impl BinaryStrings {
    fn of_length(length: usize) -> Self {
        let mut current = BitVec::with_capacity(length);
        (0..length).for_each(|_| { current.push(false); });
        BinaryStrings {
            length,
            finished: false,
            current,
        }
    }
}

impl Iterator for BinaryStrings {
    type Item = BitVec;
    fn next(self: &mut BinaryStrings) -> Option<BitVec> {
        if !self.finished {
            let to_return = self.current.clone();
            let mut iter_mut = self.current.iter_mut();
            let mut incremented = false;
            loop {
                match iter_mut.next() {
                    Some(mut idx) => {
                        if *idx {
                            *idx = false;
                            continue;
                        } else {
                            *idx = true;
                            incremented = true;
                            break;
                        }
                    },
                    None => break,
                    
                }
            }
            if incremented {
                Some(to_return)
            } else {
                self.finished = true;
                Some(to_return)
            }
        } else {
            None
        }
    }
}

impl CachedCircuit {
    fn execute(&mut self, input: &BitVec) -> BitVec {
        if self.circuit.layers.len() == 0 {
            input.clone()
        } else {
            let subcache = self.cache.entry(input.clone()).or_default();
            if subcache.len() == self.circuit.layers.len() {
                subcache[subcache.len() - 1].clone()
            } else {
                self.circuit.layers[subcache.len()..].iter().fold(input.clone(), |x, v| {
                    let y = v.execute(&x);
                    subcache.push(y.clone());
                    y
                });
                subcache[subcache.len() - 1].clone()
            }
        }
    }

    fn refines(&mut self, other: &BooleanFn) -> bool {
        let mut test = true;
        for x in BinaryStrings::of_length(self.circuit.input_size) {
            for y in BinaryStrings::of_length(self.circuit.input_size) {
                test = test && ((self.execute(&x) != self.execute(&y)) || (other.execute(&x) == other.execute(&x)));
            }
        }
        test
    }

    fn computes(&mut self, other: &BooleanFn) -> bool {
        BinaryStrings::of_length(self.circuit.input_size()).fold(true, |acc, x| { acc & (self.execute(&x) == other.execute(&x)) })
    }

    fn pop_layer(&mut self) {
        let d = self.circuit.layers.len();
        if self.circuit.layers.len() == 0 {
            panic!("can't pop layer from circuit without layers");
        } else {
            self.circuit.layers.pop();
            for (k, v) in self.cache.iter_mut() {
                if v.len() == d {
                    v.pop();
                }
            }
        }
    }

    fn push_layer(&mut self, layer: Layer) {
        self.circuit.push_layer(layer);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binary_strings() {
        assert_eq!(
            BinaryStrings::of_length(1).collect::<Vec<BitVec>>()
            , vec![ bitvec![LocalBits, usize; 0]
                  , bitvec![LocalBits, usize; 1]
            ]);
        assert_eq!(
            BinaryStrings::of_length(2).collect::<Vec<BitVec>>()
            , vec![ bitvec![LocalBits, usize; 0, 0]
                  , bitvec![LocalBits, usize; 1, 0]
                  , bitvec![LocalBits, usize; 0, 1]
                  , bitvec![LocalBits, usize; 1, 1]
            ]);
        assert_eq!(
            BinaryStrings::of_length(3).collect::<Vec<BitVec>>()
            , vec![ bitvec![LocalBits, usize; 0, 0, 0]
                  , bitvec![LocalBits, usize; 1, 0, 0]
                  , bitvec![LocalBits, usize; 0, 1, 0]
                  , bitvec![LocalBits, usize; 1, 1, 0]
                  , bitvec![LocalBits, usize; 0, 0, 1]
                  , bitvec![LocalBits, usize; 1, 0, 1]
                  , bitvec![LocalBits, usize; 0, 1, 1]
                  , bitvec![LocalBits, usize; 1, 1, 1]
            ]);
    }

    #[test]
    fn xor_circuit_computes_xor_fn() {
        let test = |n| {
            let xor_fn = BooleanFn::xor(n);
            let mut cached_circuit = Circuit::xor(n).cached();
            assert!(cached_circuit.computes(&xor_fn));
        };
        for i in (1..9).into_iter() {
            test(i);
        }
    }

    #[test]
    fn xor_circuit_refines_xor_fn() {
        let test = |n| {
            let xor_fn = BooleanFn::xor(n);
            let mut cached_circuit = Circuit::xor(n).cached();
            for i in (0..cached_circuit.circuit.layers.len()).into_iter() {
                assert!(cached_circuit.refines(&xor_fn));
                cached_circuit.pop_layer();
            }
        };
        for i in (1..4).into_iter() {
            test(i);
        }
    }
}

fn main() {
}
