use anyhow::Result;

use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::util::timing::TimingTree;
use plonky2_sha512::circuit::array_to_bits;
use rand::Rng;
use crate::circuit::make_smt_circuit;

mod circuit;
mod smt;

const EXPECTED_RES: [u8; 512] = [
    0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0,
    1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1,
    0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1,
    0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0,
    1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1,
    1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0,
    1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1,
    1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1,
    1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0,
    1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1,
    0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1,
    0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1,
    0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0,
    0, 1,
];

fn main() {
    println!("Hello, world!");
    let mut msg = vec![0; 128 as usize];
    for i in 0..127 {
        msg[i] = 0 as u8;
    }

    prove_binary_node(&msg.clone(), &msg.clone());
    // other_test();
}


pub fn prove_binary_node(
    m1: &[u8],
    m2: &[u8]
) {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let len = m1.len() * 8;
    let smt_circuit = make_smt_circuit(&mut builder, 3, len as u128);

    let mut pw = PartialWitness::<F>::new();

    let m1_bits = array_to_bits(m1);
    //let m2_bits = array_to_bits(m2);
    // println!("{} {}", m1_bits.len(), m2_bits.len());


    for i in 0..len {
        pw.set_bool_target(smt_circuit.data[i], m1_bits[i]);
        //pw.set_bool_target(sha512_circuit.message[256+i], m2_bits[i]);
    }

    for i in 0..EXPECTED_RES.len() {
        if EXPECTED_RES[i] == 1 {
            builder.assert_one(smt_circuit.root[i].target);
        } else {
            builder.assert_zero(smt_circuit.root[i].target);
        }
    }

    let data = builder.build::<C>();
    let proof = data.prove(pw).unwrap();

    data.verify(proof.clone()).expect("verify error");
    println!("done!!!")
    // test_serialization(&proof, &data.verifier_only, &data.common)?;

}

pub fn other_test() {
    let mut msg = vec![0; 128 as usize];
    for i in 0..127 {
        msg[i] = i as u8;
    }

    let msg_bits = array_to_bits(&msg);
    let len = msg.len() * 8;
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let targets = plonky2_sha512::circuit::make_circuits(&mut builder, len as u128);
    let mut pw = PartialWitness::new();

    for i in 0..len {
        pw.set_bool_target(targets.message[i], msg_bits[i]);
    }

    let mut rng = rand::thread_rng();
    let rnd = rng.gen_range(0..512);
    for i in 0..EXPECTED_RES.len() {
        let b = (i == rnd && EXPECTED_RES[i] != 1) || (i != rnd && EXPECTED_RES[i] == 1);
        if b {
            builder.assert_one(targets.digest[i].target);
        } else {
            builder.assert_zero(targets.digest[i].target);
        }
    }

    let data = builder.build::<C>();
    let proof = data.prove(pw).unwrap();

    data.verify(proof).expect("");
}
