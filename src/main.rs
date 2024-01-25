
use eth_types::Field;

#[derive(Clone, Debug)]
pub struct ExpCircuitConfig {
    q_running: Selector, // active on rows 1..256
    q_first: Selector, // active on row 0
    q_last: Selector, // active on row 257
    running_result: Column<Advice>, // row 0 is 1, rows 1..256 are prod(x^(2^i)^e_(i-1)), row 257 is input result
    running_base_powers: Column<Advice>, // row 0 is any, row 1 is input base, rows 2..257 are x^(2^i)
    running_exponent: Column<Advice> // rows 0..255 are are the reverse elements of recursion e_next=e_prev*2+e_(255-i), row 256 is 0, row 257 is input exponent
    exponent_bits: Column<Advice>, // row 0 is any, rows 1..256 are e_i
}

#[derive(Clone, Debug, Default)]
pub struct ExpCircuit<F>{
    base: F, 
    exponent: F,
    result: F,
}

impl<F:FieldExt> Circuit<F> for ExpCircuit<F> {
    type Config = ExpCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_running = meta.selector();
        let q_first = meta.selector();
        let q_last = meta.selector();
        let running_result = meta.advice_column();
        let running_base_powers = meta.advice_column();
        let running_exponent = meta.advice_column();
        let exponent_bits = meta.advice_column();

        meta.create_gate("INITIAL VALUES", |meta| { 
            let q_first = meta.query_selector(q_first);
            let result_init = meta.query_advice(running_result, Rotatin::cur());
            let exponent_init = meta.query_advice(running_exponent, Rotation(256));
            let mut gate = vec![];
            gate.push(("check running result default case", q_first * (result_init - 1)));
            gate.push(("check running exponent default case", q_first * (exponent_init - 0)));
            gate
        });

        meta.create_gate("FINAL VALUES", |meta| {
            let q_last = meta.query_selector(q_last);
            let result_input = meta.query_advice(running_result, Rotation::cur());
            let result_output = meta.query_advice(running_result, Rotation::prev());
            let exponent_input = metaa.query_advice(running_exponent, Rotatin::cur());
            let exponent_output = meta.query_advice(running_exponent, Rotation(-257));
            let mut gate = vec![];
            gate.push(("check running result output", q_last * (result_input - result_output)));
            gate.push(("check running exponent output", q_last * (exponent_input - exponent_output)));
            gate
        });

        meta.create_gate("RUNNING VALUES", |meta| {
            let q_running = meta.query_selector(q_running);
            let result_next = meta.query_advice(running_result, Rotation::cur());
            let result_prev = meta.query_advice(running_result, Rotation::prev());
            let x2i = meta.query_advice(running_base_powers, Rotation::cur());
            let ei = meta.query_advice(exponent_bits, Rotation::cur());
            let x2i_prev = x2i.clone();
            let x2i_next = meta.query_advice(running_base_powers, Rotation::next());
            let e_next = meta.query_advice(running_exponent, Rotation::prev());
            let e_prev = meta.query_advice(running_exponent, Rotation::cur());
            let mut gate = vec![];
            gate.push(("check running result step case", q_running * (result_next - result_prev * (x2i * ei + (1 - ei)))));
            gate.push(("check running base powers step case", q_running * (x2i_next - x2i_prev * x2i_prev)));
            gate.push(("check running exponent step case", q_running * (e_next - (ei + 2 * e_prev)));
            gate.push(("check exponent bits are bits", q_running * ei * (1 - ei)))
            gate
        });

        BlobKZGConfig {
            q_running,
            q_first,
            q_last,
            running_result,
            running_base_powers,
            running_exponent,
            exponent_bits
        }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let running_result: [F;257] = {
            let mut running_result = [F::default(); 257];
            running_result[0] = 1;
            for i in 1..=256 {
                if exponent_bits[i-1]==1 {
                    running_result[i] = running_result[i-1] * running_base_powers[i]
                } else {
                    running_result[i] = running_result[i-1];
                }
            }
            running_result
        };

        let running_base_powers: [F; 257] = {
            let mut runnng_base_powers = [F::default(); 257];
            running_base_powers[0] = self.base;
            for i in 1..=256 {
                running_base_powers[i] = running_base_powers[i-1] * running_base_powers[i-1];
            }
            running_base_powers
        };

        let exponent_bits: [F; 256] = {
            let mut exponent_bits = [F::default(); 256];
            let exponent_bytes: [u8;32] = self.exponent.to_repr().as_ref().try_into().unwrap();
            for j in 0..32 {
                for i in 0..8 {
                    if ((exponent_bytes[j]>>i) & 1) == 1 {
                        exponent_bits[j*8+i] = F::one();
                    } else {
                        exponent_bits[j*8+i] = F::zero();
                    }
                }
            }
            exponent_bits
        };

        let running_exponent: [F;257] = {
            let mut running_exponent = [F::default; 257];
            running_exponent[0] = 0;
            for i in 1..=256 {
                running_exponent[i] = running_exponent[i-1]*2 + exponent_bits[256-i];
            }
            running_exponent
        };
        
        layouter.assign_region(|| "ExpCircuit Region", |mut region| {
            // SELECTOR: q_running
            for i in 1..=256 {
                config.q_running.enable(&mut region, i)?;
            }

            // SELECTOR: q_first
            config.q_first.enable(&mut region, 0)?;

            // SELECTOR: q_last
            config.q_last.enable(&mut region, 257)?;

            // COLUMN: running_result
            for i in 0..=256 {
                region.assign_advice(|| "running result", config.running_result, i, || Value::known(running_result[i]));
            }
            regin.assign_advice(|| "input result", config.running_result, 257, || Value::known(self.result));

            // COLUMN: running_base_powers
            for i in 1..=257 {
                region.assign_advice(|| "running base input and powers", config.running_base_powers, i, || Value::known(running_base_powers[i-1]));
            }

            // COLUMN: running_exponent
            for i in 0..=256 {
                region.assign_advice(|| "reverse running exponent values", config.running_exponent, i, || Value::known(running_exponent[256-i]));
            }
            region.assign_advice(|| "input exponent", config.running_exponent, 257, || Value::known(self.exponent));
            
            // COLUMN: exponent_bits
            for i in 1..=256 {
                region.assign_advice(|| "exponent bits", config.exponent_bits, i, || Value::known(exponent_bits[i-1]));
            }

            region.name_column(|| "running_result", config.running_result);
            region.name_column(|| "running_base_powers", config.running_base_powers);
            region.name_column(|| "running_exponent", config.running_exponent);
            region.name_column(|| "exponent_bits", config.exponent_bits);
            Ok(())
        })?;
        Ok(())
    }
}

fn main() {
    type F = halo2_proofs::halo2curves::bn256::Fr; // Native Field
    let (base, exponent, result) = (F::from(5), F::from(6), base.pow(exponent));
    println!("base: {base:?}, exponent: {exponent:?}, result: {result:?}, MODULUS: {}", F::MODULUS);
    let circuit = ExpCircuit::<F>{base, exponent, result};
    let prover = hal2_proofs::dev::MockProver::<N>::run(10, &circuit, vec![]).unwrap();
    prover.assert_satisfied();
    println!("CIRCUIT TEST COMPLETED")
}