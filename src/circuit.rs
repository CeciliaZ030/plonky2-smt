use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2_sha512::circuit::Sha512Targets;
use plonky2_sha512::circuit::make_circuits as make_sha512_circuits;

pub struct SMTTargets{
    pub data: Vec<BoolTarget>,
    // (direction: left=0, right=1, hash)
    pub path_hashes: Vec< Vec<BoolTarget>>,
    pub path_nodes: Vec<Sha512Targets>,
    pub root: Vec<BoolTarget>,
}

pub fn make_smt_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    height: usize,
    leaf_size: u128
) -> SMTTargets {

    let mut leaf = make_sha512_circuits(builder, leaf_size);

    let mut path_hashes: Vec<Vec<BoolTarget>> = Vec::new();
    for i in 0..height-1 {
        path_hashes.push(
            (0..512)
                .map(|_| builder.add_virtual_bool_target_unsafe())
                .collect()
        );
    }

    let mut path_nodes = Vec::new();
    let first_node = make_sha512_circuits(builder, 512*2);
    connect_nodes(builder, &first_node, &leaf, &path_hashes[0]);
    path_nodes.push(first_node);
    for i in 1..height-1 {
        let node = make_sha512_circuits(builder, 512*2);
        connect_nodes(builder, &node, &path_nodes[i-1], &path_hashes[i]);
        path_nodes.push(node);
    }

    SMTTargets {
        data: leaf.message,
        path_hashes,
        path_nodes,
        root: path_nodes[height-2].clone()
    }
}

// Todo: the construction should be recursive! This only supports left-most data


pub fn build_left_node<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    parent: &Sha512Targets,
    left_child: &Sha512Targets,
    right_child: &Vec<BoolTarget>
) {
    for i in 0..512 {
        builder.connect(parent.message[i].target.clone(), left_child.digest[i].target.clone());
    }
    for i in 512..512*2 {
        builder.connect(parent.message[i].target.clone(), right_child[i].target.clone());
    }
}

pub fn build_right_node<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    parent: &Sha512Targets,
    left_child: &Vec<BoolTarget>,
    right_child: &Sha512Targets,
) {
    for i in 0..512 {
        builder.connect(parent.message[i].target.clone(), left_child[i].target.clone());
    }
    for i in 512..512*2 {
        builder.connect(parent.message[i].target.clone(), right_child.digest[i].target.clone());
    }
}
