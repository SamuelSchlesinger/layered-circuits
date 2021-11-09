#![feature(map_first_last)]
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

impl<T> Lit<T> {
    /// Sometimes we just want to know which input we're looking at,
    /// not what its sign is
    fn underlying(&self) -> &T {
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

    fn execute(&self, input: &BitVec) -> BitVec {
        let mut output = BitVec::new();
        for g in &self.gates {
            output.push(g.gate_type.compute(
                g.gate_inputs.0.negated() ^ input[*g.gate_inputs.0.underlying()],
                g.gate_inputs.1.negated() ^ input[*g.gate_inputs.1.underlying()],
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
    function: fn(BitVec) -> BitVec,
}

struct CachedCircuit {
    circuit: Circuit,
    cache: BTreeMap<BitVec, Vec<BitVec>>,
}

impl Circuit {
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

    fn add_layer(&mut self, layer: Layer) {
        self.layers.push(layer);
    }
}

fn fill_subcache(circuit: &mut Circuit, subcache: &mut Vec<BitVec>, d: usize, i: &BitVec) {
    circuit.layers[d..].iter().fold(i.clone(), |x, v| {
        let y = v.execute(&x);
        subcache.push(y.clone());
        y
    });
}

impl CachedCircuit {
    fn execute(&mut self, input: &BitVec) -> &BitVec {
        let subcache = self.cache.entry(input.clone()).or_default();
        if subcache.len() == self.circuit.layers.len() {
            &subcache[subcache.len() - 1]
        } else {
            fill_subcache(&mut self.circuit, subcache, subcache.len(), input);
            &subcache[subcache.len() - 1]
        }
    }
}

fn main() {
    let mut circuit = Circuit::new(2);
    circuit.add_layer(Layer::new(vec![
        Gate::and(Lit::Not(0), Lit::NotNot(1)),
        Gate::and(Lit::NotNot(0), Lit::Not(1)),
    ]));
    circuit.add_layer(Layer::new(vec![
        Gate::or(Lit::NotNot(0), Lit::NotNot(1))
    ]));
    let input0 = bitvec![LocalBits, usize; 0, 0];
    let input1 = bitvec![LocalBits, usize; 0, 1];
    let mut cached_circuit = circuit.cached();
    cached_circuit.execute(&input0);
    cached_circuit.execute(&input1);
    println!("{:?}", cached_circuit.execute(&input1));
}