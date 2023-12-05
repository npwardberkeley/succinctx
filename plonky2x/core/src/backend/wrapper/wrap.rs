use std::fs::{self, File};
use std::path::Path;

use anyhow::Result;
use log::{debug, info};
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_data::{
    CommonCircuitData, VerifierCircuitTarget, VerifierOnlyCircuitData,
};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig};
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};
use plonky2_evm::all_stark::AllStark;
use plonky2_evm::config::StarkConfig;
use plonky2_evm::fixed_recursive_verifier::AllRecursiveCircuits;
use plonky2_evm::proof::PublicValues;
use plonky2x_derive::CircuitVariable;
use serde::Serialize;

use crate::backend::circuit::{CircuitBuild, PlonkParameters};
use crate::frontend::builder::CircuitBuilder;
use crate::frontend::vars::{ByteVariable, CircuitVariable, EvmVariable, Variable};
use crate::prelude::U32Variable;

pub fn get_sample_circuits_and_proof_from_serialized<F, C, const D: usize>() -> Result<(
    AllRecursiveCircuits<F, C, D>,
    ProofWithPublicInputs<F, C, D>,
    PublicValues,
)>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
{
    let all_stark = AllStark::<F, D>::default();
    let config = StarkConfig::standard_fast_config();

    let all_circuits = AllRecursiveCircuits::<F, C, D>::new(
        &all_stark,
        &[16..17, 11..13, 17..19, 14..15, 9..11, 12..13, 19..21],
        &config,
    );

    // read from files
    let block_proof_json =
        std::fs::read_to_string("../verifier/data/recursive/block_proof.json").unwrap();
    let block_public_values_json =
        std::fs::read_to_string("../verifier/data/recursive/block_public_values.json").unwrap();

    // deserialize
    let block_proof: ProofWithPublicInputs<F, C, D> =
        serde_json::from_str(&block_proof_json).unwrap();
    let block_public_values: PublicValues =
        serde_json::from_str(&block_public_values_json).unwrap();

    Ok((all_circuits, block_proof, block_public_values))
}

#[derive(Debug)]
pub struct WrappedCircuit<
    InnerParameters: PlonkParameters<D>,
    OuterParameters: PlonkParameters<D, Field = InnerParameters::Field>,
    const D: usize,
> where
    <InnerParameters::Config as GenericConfig<D>>::Hasher: AlgebraicHasher<InnerParameters::Field>,
{
    circuit: CircuitBuild<InnerParameters, D>,
    hash_circuit: CircuitBuild<InnerParameters, D>,
    circuit_proof_target: ProofWithPublicInputsTarget<D>,
    circuit_verifier_target: VerifierCircuitTarget,
    recursive_circuit: CircuitBuild<InnerParameters, D>,
    hash_verifier_target: VerifierCircuitTarget,
    hash_proof_target: ProofWithPublicInputsTarget<D>,
    pub wrapper_circuit: CircuitBuild<OuterParameters, D>,
    proof_target: ProofWithPublicInputsTarget<D>,
    verifier_target: VerifierCircuitTarget,
}

impl<
        InnerParameters: PlonkParameters<D>,
        OuterParameters: PlonkParameters<D, Field = InnerParameters::Field>,
        const D: usize,
    > WrappedCircuit<InnerParameters, OuterParameters, D>
where
    <InnerParameters::Config as GenericConfig<D>>::Hasher: AlgebraicHasher<InnerParameters::Field>,
{
    pub fn build(circuit: CircuitBuild<InnerParameters, D>) -> Self {
        // Standartize the public inputs/outputs to their hash and verify the circuit recursively.
        let mut hash_builder = CircuitBuilder::<InnerParameters, D>::new();
        let circuit_proof_target = hash_builder.add_virtual_proof_with_pis(&circuit.data.common);
        let circuit_verifier_target =
            hash_builder.constant_verifier_data::<InnerParameters>(&circuit.data);
        hash_builder.verify_proof::<InnerParameters>(
            &circuit_proof_target,
            &circuit_verifier_target,
            &circuit.data.common,
        );

        let num_input_targets = circuit.io.input().len();
        let (input_targets, output_targets) = circuit_proof_target
            .public_inputs
            .split_at(num_input_targets);

        let input_bytes = input_targets
            .chunks_exact(ByteVariable::nb_elements())
            .map(ByteVariable::from_targets)
            .collect::<Vec<_>>();
        let output_bytes = output_targets
            .chunks_exact(ByteVariable::nb_elements())
            .map(ByteVariable::from_targets)
            .collect::<Vec<_>>();

        hash_builder.watch_slice(&input_bytes, "input_bytes");
        hash_builder.watch_slice(&output_bytes, "output_bytes");

        let input_hash = hash_builder.curta_sha256(&input_bytes);
        let output_hash = hash_builder.curta_sha256(&output_bytes);

        hash_builder.watch(&input_hash, "input_hash");
        hash_builder.watch(&output_hash, "output_hash");

        // We must truncate the top 3 bits because in the gnark-plonky2-verifier, the input_hash
        // and output_hash are both represented as 1 field element in the BN254 field to reduce
        // onchain verification costs.
        let input_hash_zeroed = hash_builder.mask_be_bits(input_hash, 3);
        let output_hash_zeroed = hash_builder.mask_be_bits(output_hash, 3);

        hash_builder.watch(&input_hash_zeroed, "input_hash_truncated");
        hash_builder.watch(&output_hash_zeroed, "output_hash_truncated");

        let input_vars = input_hash_zeroed
            .as_bytes()
            .iter()
            .map(|b| b.to_variable(&mut hash_builder))
            .collect::<Vec<Variable>>();

        let output_vars = output_hash_zeroed
            .as_bytes()
            .iter()
            .map(|b| b.to_variable(&mut hash_builder))
            .collect::<Vec<Variable>>();

        hash_builder.watch_slice(&input_vars, "input_hash_truncated as vars");
        hash_builder.watch_slice(&output_vars, "output_hash_truncated as vars");

        // Write input_hash, output_hash to public_inputs. In the gnark-plonky2-verifier, these
        // 64 bytes get summed to 2 field elements that correspond to the input_hash and output_hash
        // respectively as public inputs.
        input_vars
            .clone()
            .into_iter()
            .chain(output_vars)
            .for_each(|v| {
                hash_builder.write(v);
            });
        let hash_circuit = hash_builder.build();

        // An inner recursion to standardize the degree.
        let mut recursive_builder = CircuitBuilder::<InnerParameters, D>::new();
        let hash_proof_target =
            recursive_builder.add_virtual_proof_with_pis(&hash_circuit.data.common);
        let hash_verifier_target =
            recursive_builder.constant_verifier_data::<InnerParameters>(&hash_circuit.data);
        recursive_builder.verify_proof::<InnerParameters>(
            &hash_proof_target,
            &hash_verifier_target,
            &hash_circuit.data.common,
        );
        assert_eq!(hash_proof_target.public_inputs.len(), 32usize * 2);

        recursive_builder
            .api
            .register_public_inputs(&hash_proof_target.public_inputs);

        let recursive_circuit = recursive_builder.build();
        debug!(
            "Recursive circuit degree: {}",
            recursive_circuit.data.common.degree()
        );

        // Finally, wrap this in the outer circuit.
        let mut wrapper_builder = CircuitBuilder::<OuterParameters, D>::new();
        let proof_target =
            wrapper_builder.add_virtual_proof_with_pis(&recursive_circuit.data.common);
        let verifier_target =
            wrapper_builder.constant_verifier_data::<InnerParameters>(&recursive_circuit.data);
        wrapper_builder.verify_proof::<InnerParameters>(
            &proof_target,
            &verifier_target,
            &recursive_circuit.data.common,
        );

        wrapper_builder
            .api
            .register_public_inputs(&proof_target.public_inputs);

        let wrapper_circuit = wrapper_builder.build();
        debug!(
            "Wrapped circuit degree: {}",
            wrapper_circuit.data.common.degree()
        );

        Self {
            circuit,
            hash_circuit,
            recursive_circuit,
            circuit_proof_target,
            circuit_verifier_target,
            hash_proof_target,
            hash_verifier_target,
            wrapper_circuit,
            proof_target,
            verifier_target,
        }
    }

    pub fn prove(
        &self,
        inner_proof: &ProofWithPublicInputs<InnerParameters::Field, InnerParameters::Config, D>,
    ) -> Result<WrappedOutput<OuterParameters, D>> {
        let mut pw = PartialWitness::new();
        pw.set_verifier_data_target(
            &self.circuit_verifier_target,
            &self.circuit.data.verifier_only,
        );
        pw.set_proof_with_pis_target(&self.circuit_proof_target, inner_proof);

        let (hash_proof, _) = self.hash_circuit.prove_with_partial_witness(pw);
        self.hash_circuit.data.verify(hash_proof.clone())?;
        debug!("Successfully verified hash proof");

        let mut pw = PartialWitness::new();
        pw.set_verifier_data_target(
            &self.hash_verifier_target,
            &self.hash_circuit.data.verifier_only,
        );
        pw.set_proof_with_pis_target(&self.hash_proof_target, &hash_proof);

        let recursive_proof = self.recursive_circuit.data.prove(pw)?;
        self.recursive_circuit
            .data
            .verify(recursive_proof.clone())?;
        debug!("Successfully verified recursive proof");

        let mut pw = PartialWitness::new();
        pw.set_verifier_data_target(
            &self.verifier_target,
            &self.recursive_circuit.data.verifier_only,
        );
        pw.set_proof_with_pis_target(&self.proof_target, &recursive_proof);

        let proof = self.wrapper_circuit.data.prove(pw)?;
        self.wrapper_circuit.data.verify(proof.clone())?;
        debug!("Successfully verified wrapper proof");

        Ok(WrappedOutput {
            proof,
            common_data: self.wrapper_circuit.data.common.clone(),
            verifier_data: self.wrapper_circuit.data.verifier_only.clone(),
        })
    }
}

#[derive(Debug)]
pub struct WrappedOutput<L: PlonkParameters<D>, const D: usize> {
    pub proof: ProofWithPublicInputs<L::Field, L::Config, D>,
    pub common_data: CommonCircuitData<L::Field, D>,
    pub verifier_data: VerifierOnlyCircuitData<L::Config, D>,
}

impl<L: PlonkParameters<D>, const D: usize> WrappedOutput<L, D> {
    pub fn save<P: AsRef<Path>>(&self, path: P) -> Result<()>
    where
        L::Config: Serialize,
    {
        if !path.as_ref().exists() {
            fs::create_dir_all(&path)?;
        }
        let common_data_file = File::create(path.as_ref().join("common_circuit_data.json"))?;
        serde_json::to_writer(&common_data_file, &self.common_data)?;
        info!("Succesfully wrote common circuit data to common_circuit_data.json");

        let verifier_data_file =
            File::create(path.as_ref().join("verifier_only_circuit_data.json"))?;
        serde_json::to_writer(&verifier_data_file, &self.verifier_data)?;
        info!("Succesfully wrote verifier data to verifier_only_circuit_data.json");

        let proof_file = File::create(path.as_ref().join("proof_with_public_inputs.json"))?;
        serde_json::to_writer(&proof_file, &self.proof)?;
        info!("Succesfully wrote proof to proof_with_public_inputs.json");

        Ok(())
    }
}

#[derive(Clone, Debug, CircuitVariable)]
#[value_name(U160Value)]
pub struct U160Variable {
    // These limbs are little-endian
    pub limbs: [U32Variable; 5],
}

impl EvmVariable for U160Variable {
    fn encode<L: PlonkParameters<D>, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<L, D>,
    ) -> Vec<ByteVariable> {
        self.limbs
            .iter()
            .rev()
            .flat_map(|limb| limb.encode(builder))
            .collect()
    }

    fn decode<L: PlonkParameters<D>, const D: usize>(
        builder: &mut CircuitBuilder<L, D>,
        bytes: &[ByteVariable],
    ) -> Self {
        let mut limbs = vec![];
        for i in 0..5 {
            limbs.push(U32Variable::decode(builder, &bytes[i * 4..(i + 1) * 4]));
        }
        limbs.reverse();
        Self {
            limbs: limbs.try_into().unwrap(),
        }
    }

    fn encode_value<F: RichField>(value: Self::ValueType<F>) -> Vec<u8> {
        let mut bytes = vec![];
        // Iterate over the limbs big-endian
        for limb in value.limbs.iter().rev() {
            bytes.extend_from_slice(&U32Variable::encode_value::<F>(*limb));
        }
        bytes
    }

    fn decode_value<F: RichField>(bytes: &[u8]) -> Self::ValueType<F> {
        let mut limbs = vec![];
        for i in 0..5 {
            limbs.push(U32Variable::decode_value::<F>(&bytes[i * 4..(i + 1) * 4]));
        }
        // Store the limbs as little-endian
        limbs.reverse();
        Self::ValueType::<F> {
            limbs: limbs.try_into().unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::collections::BTreeMap;

    use ethereum_types::U256;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::hash::hash_types::RichField;
    use plonky2::plonk::config::PoseidonGoldilocksConfig;

    use super::*;
    use crate::backend::circuit::{Circuit, DefaultParameters, Groth16WrapperParameters};
    use crate::frontend::builder::{CircuitBuilder, CircuitIO};
    use crate::frontend::uint::uint256::U256Variable;
    use crate::frontend::uint::uint32::U32Variable;
    use crate::frontend::uint::uint64::U64Variable;
    use crate::utils;

    fn hex_str_to_u256(hex: &str) -> U256 {
        let value = U256::from_str_radix(&hex[2..], 16).expect("Failed to convert to U256");
        value
    }

    fn hex_str_to_u160<F: RichField>(hex: &str) -> U160Value<F> {
        U160Value::<F> {
            limbs: [
                u32::from_str_radix(&hex[34..42], 16).expect("Failed to convert to u32"),
                u32::from_str_radix(&hex[26..34], 16).expect("Failed to convert to u32"),
                u32::from_str_radix(&hex[18..26], 16).expect("Failed to convert to u32"),
                u32::from_str_radix(&hex[10..18], 16).expect("Failed to convert to u32"),
                u32::from_str_radix(&hex[2..10], 16).expect("Failed to convert to u32"),
            ],
        }
    }

    #[test]
    #[cfg_attr(feature = "ci", ignore)]
    fn test_wrapper() {
        const D: usize = 2;
        type InnerParameters = DefaultParameters;
        type OuterParameters = Groth16WrapperParameters;

        utils::setup_logger();

        let build_path = "../verifier/data".to_string();
        let path = format!("{}/test_circuit/", build_path);
        let dummy_path = format!("{}/dummy/", build_path);

        // Create an inner circuit for verification.
        let mut builder = CircuitBuilder::<DefaultParameters, 2>::new();
        let a = builder.evm_read::<ByteVariable>();
        let b = builder.evm_read::<ByteVariable>();
        let c = builder.xor(a, b);
        builder.evm_write(c);

        // Set up the dummy circuit and wrapper.
        let dummy_circuit = builder.build();
        let mut dummy_input = dummy_circuit.input();
        dummy_input.evm_write::<ByteVariable>(0u8);
        dummy_input.evm_write::<ByteVariable>(1u8);
        let (dummy_inner_proof, dummy_output) = dummy_circuit.prove(&dummy_input);
        dummy_circuit.verify(&dummy_inner_proof, &dummy_input, &dummy_output);
        println!("Verified dummy_circuit");

        let dummy_wrapper =
            WrappedCircuit::<InnerParameters, OuterParameters, D>::build(dummy_circuit);
        let dummy_wrapped_proof = dummy_wrapper.prove(&dummy_inner_proof).unwrap();
        dummy_wrapped_proof.save(dummy_path).unwrap();
        println!("Saved dummy_circuit");

        // Set up a inner circuit and wrapper.
        let mut builder = CircuitBuilder::<DefaultParameters, 2>::new();
        let a = builder.evm_read::<ByteVariable>();
        let _ = builder.evm_read::<ByteVariable>();
        builder.evm_write(a);

        let circuit = builder.build();
        let mut input = circuit.input();
        input.evm_write::<ByteVariable>(0u8);
        input.evm_write::<ByteVariable>(0u8);
        let (proof, _output) = circuit.prove(&input);

        let wrapped_circuit = WrappedCircuit::<InnerParameters, OuterParameters, D>::build(circuit);

        assert_eq!(
            wrapped_circuit.wrapper_circuit.data.common,
            dummy_wrapper.wrapper_circuit.data.common,
        );

        let wrapped_proof = wrapped_circuit.prove(&proof).unwrap();
        wrapped_proof.save(path).unwrap();
    }

    #[test]
    fn test_wrapper_fibonacci() {
        const D: usize = 2;
        type InnerParameters = DefaultParameters;
        type OuterParameters = Groth16WrapperParameters;

        utils::setup_logger();

        let build_path = "../verifier/data".to_string();
        let path = format!("{}/fibonacci/", build_path);

        // Create an inner circuit for verification.
        let mut builder = CircuitBuilder::<DefaultParameters, 2>::new();

        // The arithmetic circuit.
        let initial_a = builder.evm_read::<U64Variable>();
        let initial_b = builder.evm_read::<U64Variable>();
        let mut prev_target = initial_a;
        let mut cur_target = initial_b;
        for _ in 0..99 {
            let temp = builder.add(prev_target, cur_target);
            prev_target = cur_target;
            cur_target = temp;
        }

        builder.evm_write(cur_target);

        let circuit = builder.build();
        let mut input = circuit.input();
        input.evm_write::<U64Variable>(0);
        input.evm_write::<U64Variable>(1);
        let (proof, output) = circuit.prove(&input);

        dbg!(output);

        let wrapped_circuit = WrappedCircuit::<InnerParameters, OuterParameters, D>::build(circuit);

        let wrapped_proof = wrapped_circuit.prove(&proof).unwrap();
        wrapped_proof.save(path).unwrap();
    }

    #[test]
    fn test_wrapper_recursive() {
        const D: usize = 2;
        type InnerParameters = DefaultParameters;
        type OuterParameters = Groth16WrapperParameters;

        utils::setup_logger();

        let build_path = "../verifier/data".to_string();
        let path = format!("{}/recursive/", build_path);

        // Create an inner circuit for verification.
        let mut builder = CircuitBuilder::<DefaultParameters, 2>::new();

        // The arithmetic circuit.
        let _state_root_before = builder.evm_read::<U256Variable>();
        let _transactions_root_before = builder.evm_read::<U256Variable>();
        let _receipts_root_before = builder.evm_read::<U256Variable>();

        let _state_root_after = builder.evm_read::<U256Variable>();
        let _transactions_root_after = builder.evm_read::<U256Variable>();
        let _receipts_root_after = builder.evm_read::<U256Variable>();

        let _block_beneficiary = builder.evm_read::<U160Variable>();
        let _block_timestamp = builder.evm_read::<U256Variable>();
        let _block_number = builder.evm_read::<U256Variable>();
        let _block_difficulty = builder.evm_read::<U256Variable>();
        let _block_random = builder.evm_read::<U256Variable>();
        let _block_gaslimit = builder.evm_read::<U256Variable>();
        let _block_chain_id = builder.evm_read::<U256Variable>();
        let _block_base_fee = builder.evm_read::<U256Variable>();
        let _block_gas_used = builder.evm_read::<U256Variable>();

        let _block_bloom = (0..8)
            .map(|_| builder.evm_read::<U256Variable>())
            .collect::<Vec<_>>();

        let _prev_hashes = (0..256)
            .map(|_| builder.evm_read::<U256Variable>())
            .collect::<Vec<_>>();
        let _cur_hash = builder.evm_read::<U256Variable>();

        let _genesis_state_trie_root = builder.evm_read::<U256Variable>();
        let _txn_number_before = builder.evm_read::<U256Variable>();
        let _txn_number_after = builder.evm_read::<U256Variable>();
        let _gas_used_before = builder.evm_read::<U256Variable>();
        let _gas_used_after = builder.evm_read::<U256Variable>();
        let _block_boom_before = (0..8)
            .map(|_| builder.evm_read::<U256Variable>())
            .collect::<Vec<_>>();
        let _block_boom_after = (0..8)
            .map(|_| builder.evm_read::<U256Variable>())
            .collect::<Vec<_>>();

        let circuit = builder.build();
        let mut input = circuit.input();

        // trie_roots_before
        // state_root
        input.evm_write::<U256Variable>(hex_str_to_u256(
            "0x82648888855b1d41b36ea681a16ef84852e34e6011d028f278438adb4e8e30b4",
        ));
        // transactions_root
        input.evm_write::<U256Variable>(hex_str_to_u256(
            "0x56e81f171bcc55a6ff8345e682c0f86e5b48e01b886cadc001622fb5e363b421",
        ));
        // receipts_root
        input.evm_write::<U256Variable>(hex_str_to_u256(
            "0x56e81f171bcc55a6ff8345e682c0f86e5b48e01b886cadc001622fb5e363b421",
        ));

        // trie_roots_after
        // state_root
        input.evm_write::<U256Variable>(hex_str_to_u256(
            "0x048e45aef8dac161e0cec0edacd8af5b3388700affad6ede63b33c5d0ec786f5",
        ));
        // transactions_root
        input.evm_write::<U256Variable>(hex_str_to_u256(
            "0xc523d7b87c0e48a24dae53b3e3be716e5a6808c1e05216487655c0ad84b12236",
        ));
        // receipts_root
        input.evm_write::<U256Variable>(hex_str_to_u256(
            "0xfc047c8c86ea3d317bf5b0886e85c242ecc625efd3f7da721c438aff8331b2ab",
        ));

        // block_metadata
        // block_beneficiary
        let val = hex_str_to_u160("0x2adc25665018aa1fe0e6bc666dac8fc2687ff8ba");
        input.evm_write::<U160Variable>(val);
        // block_timestamp
        input.evm_write::<U256Variable>(U256::from(1000));
        // block_number
        input.evm_write::<U256Variable>(U256::from(0));
        // block_difficulty
        input.evm_write::<U256Variable>(U256::from(131072));
        // block_random
        input.evm_write::<U256Variable>(U256::from(0));
        // block_gaslimit
        input.evm_write::<U256Variable>(U256::from(4478310));
        // block_chain_id
        input.evm_write::<U256Variable>(U256::from(1));
        // block_base_fee
        input.evm_write::<U256Variable>(U256::from(10));
        // block_gas_used
        input.evm_write::<U256Variable>(U256::from(43570));
        // block_bloom
        input.evm_write::<U256Variable>(U256::from(0));
        input.evm_write::<U256Variable>(U256::from(0));
        input.evm_write::<U256Variable>(
            U256::from_dec_str(
                "55213870774324510288478508388853534522527075462185808724318848722837344",
            )
            .unwrap(),
        );
        input.evm_write::<U256Variable>(
            U256::from_dec_str("1361128467683753853853488428727072845824").unwrap(),
        );
        input.evm_write::<U256Variable>(U256::from(33554432));
        input.evm_write::<U256Variable>(U256::from_dec_str("8223372036854775808").unwrap());
        input.evm_write::<U256Variable>(
            U256::from_dec_str(
                "3618502788666131106886583281521487120414687020801267626233048500247285563382",
            )
            .unwrap(),
        );
        input.evm_write::<U256Variable>(
            U256::from_dec_str("2722258584404615024560450425766186844160").unwrap(),
        );

        // block_hashes
        // prev_hashes
        for _ in 0..256 {
            input.evm_write::<U256Variable>(U256::from(0));
        }
        // cur_hash
        input.evm_write::<U256Variable>(U256::from(0));

        // extra_block_data
        // genesis_state_trie_root
        input.evm_write::<U256Variable>(hex_str_to_u256(
            "0x82648888855b1d41b36ea681a16ef84852e34e6011d028f278438adb4e8e30b4",
        ));
        // txn_number_before
        input.evm_write::<U256Variable>(U256::from(0));
        // txn_number_after
        input.evm_write::<U256Variable>(U256::from(2));
        // gas_used_before
        input.evm_write::<U256Variable>(U256::from(0));
        // gas_used_after
        input.evm_write::<U256Variable>(U256::from(43570));
        // block_boom_before
        for _ in 0..8 {
            input.evm_write::<U256Variable>(U256::from(0));
        }
        // block_boom_after
        input.evm_write::<U256Variable>(U256::from(0));
        input.evm_write::<U256Variable>(U256::from(0));
        input.evm_write::<U256Variable>(
            U256::from_dec_str(
                "55213870774324510288478508388853534522527075462185808724318848722837344",
            )
            .unwrap(),
        );
        input.evm_write::<U256Variable>(
            U256::from_dec_str("1361128467683753853853488428727072845824").unwrap(),
        );
        input.evm_write::<U256Variable>(U256::from(33554432));
        input.evm_write::<U256Variable>(U256::from_dec_str("8223372036854775808").unwrap());
        input.evm_write::<U256Variable>(
            U256::from_dec_str(
                "3618502788666131106886583281521487120414687020801267626233048500247285563382",
            )
            .unwrap(),
        );
        input.evm_write::<U256Variable>(
            U256::from_dec_str("2722258584404615024560450425766186844160").unwrap(),
        );

        let (proof, _output) = circuit.prove(&input);

        let wrapped_circuit = WrappedCircuit::<InnerParameters, OuterParameters, D>::build(circuit);

        let wrapped_proof = wrapped_circuit.prove(&proof).unwrap();
        wrapped_proof.save(path).unwrap();
    }

    #[test]
    fn test_wrapper_recursive_from_serialized() {
        type F = GoldilocksField;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;

        type InnerParameters = DefaultParameters;
        type OuterParameters = Groth16WrapperParameters;

        utils::setup_logger();

        let build_path = "../verifier/data".to_string();
        let path = format!("{}/recursive/", build_path);

        let (all_circuits, block_proof, block_public_values) =
            get_sample_circuits_and_proof_from_serialized::<F, C, D>().unwrap();

        let block_circuit = all_circuits.block.circuit;
        let block_circuit_build = CircuitBuild {
            data: block_circuit,
            io: CircuitIO::new(),
            async_hints: BTreeMap::new(),
        };

        let wrapped_circuit =
            WrappedCircuit::<InnerParameters, OuterParameters, D>::build(block_circuit_build);

        let wrapped_proof = wrapped_circuit.prove(&block_proof).unwrap();
        // wrapped_proof.save(path).unwrap();
    }
}
