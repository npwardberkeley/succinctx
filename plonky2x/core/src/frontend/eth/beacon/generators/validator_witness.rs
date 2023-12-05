use std::env;

use ethers::types::H256;
use serde::{Deserialize, Serialize};

use crate::frontend::eth::beacon::vars::{
    BeaconValidatorVariable, CompressedBeaconValidatorValue, CompressedBeaconValidatorVariable,
};
use crate::frontend::hint::simple::hint::Hint;
use crate::frontend::uint::uint64::U64Variable;
use crate::frontend::vars::ValueStream;
use crate::prelude::{ArrayVariable, Bytes32Variable, PlonkParameters};
use crate::utils::eth::beacon::BeaconClient;
use crate::utils::{bytes, bytes32, hex};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BeaconValidatorHint {}

impl<L: PlonkParameters<D>, const D: usize> Hint<L, D> for BeaconValidatorHint {
    fn hint(&self, input_stream: &mut ValueStream<L, D>, output_stream: &mut ValueStream<L, D>) {
        let client = BeaconClient::new(env::var("CONSENSUS_RPC_URL").unwrap());
        let header_root = input_stream.read_value::<Bytes32Variable>();
        let validator_index = input_stream.read_value::<U64Variable>();

        let response = client
            .get_validator_witness(hex!(header_root), validator_index)
            .unwrap();

        output_stream.write_value::<BeaconValidatorVariable>(response.validator);
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BeaconValidatorBatchHint<const B: usize> {}

impl<L: PlonkParameters<D>, const D: usize, const B: usize> Hint<L, D>
    for BeaconValidatorBatchHint<B>
{
    fn hint(&self, input_stream: &mut ValueStream<L, D>, output_stream: &mut ValueStream<L, D>) {
        let client = BeaconClient::new(env::var("CONSENSUS_RPC_URL").unwrap());
        let header_root = input_stream.read_value::<Bytes32Variable>();
        let start_idx = input_stream.read_value::<U64Variable>();
        let response = client
            .get_validator_batch_witness(hex!(header_root), start_idx, start_idx + B as u64)
            .unwrap();

        output_stream.write_value::<ArrayVariable<BeaconValidatorVariable, B>>(response);
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompressedBeaconValidatorBatchHint<const B: usize>;

impl<L: PlonkParameters<D>, const D: usize, const B: usize> Hint<L, D>
    for CompressedBeaconValidatorBatchHint<B>
{
    fn hint(&self, input_stream: &mut ValueStream<L, D>, output_stream: &mut ValueStream<L, D>) {
        let client = BeaconClient::new(env::var("CONSENSUS_RPC_URL").unwrap());
        let header_root = input_stream.read_value::<Bytes32Variable>();
        let start_idx = input_stream.read_value::<U64Variable>();
        let response = client
            .get_validator_batch_witness(hex!(header_root), start_idx, start_idx + B as u64)
            .unwrap();

        let (compressed_validators, witnesses): (
            Vec<CompressedBeaconValidatorValue<L::Field>>,
            Vec<Vec<H256>>,
        ) = response
            .iter()
            .map(|v| {
                let compressed_validator = CompressedBeaconValidatorValue::<L::Field> {
                    pubkey: bytes!(&v.pubkey),
                    withdrawal_credentials: bytes32!(v.withdrawal_credentials),
                };
                let (_, witnesses) = v.ssz_merkleize();
                let h12 = witnesses[1];
                let h22 = witnesses[5];
                (compressed_validator, vec![h12, h22])
            })
            .unzip();

        output_stream.write_value::<ArrayVariable<CompressedBeaconValidatorVariable, B>>(
            compressed_validators,
        );
        output_stream.write_value::<ArrayVariable<ArrayVariable<Bytes32Variable, 2>, B>>(witnesses);
    }
}
