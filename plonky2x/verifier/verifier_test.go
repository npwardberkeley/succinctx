package main

import (
	"os"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/logger"
	"github.com/consensys/gnark/test"
	"github.com/succinctlabs/gnark-plonky2-verifier/types"
	"github.com/succinctlabs/gnark-plonky2-verifier/variables"
)

// To run this test, you must first populate the data directory by running the following test
// in plonky2x: cargo test test_wrapper -- --nocapture
func TestPlonky2xVerifierCircuit(t *testing.T) {
	assert := test.NewAssert(t)

	testCase := func(option int64) error {
		dummyCircuitPath := "./data/dummy"
		circuitPath := "./data/recursive"

		verifierOnlyCircuitDataDummy := variables.DeserializeVerifierOnlyCircuitData(
			types.ReadVerifierOnlyCircuitData(dummyCircuitPath + "/verifier_only_circuit_data.json"),
		)
		proofWithPisDummy := variables.DeserializeProofWithPublicInputs(
			types.ReadProofWithPublicInputs(dummyCircuitPath + "/proof_with_public_inputs.json"),
		)
		commonCircuitDataDummy := types.ReadCommonCircuitData(dummyCircuitPath + "/common_circuit_data.json")

		circuit := Plonky2xVerifierCircuit{
			ProofWithPis:      proofWithPisDummy,
			VerifierData:      verifierOnlyCircuitDataDummy,
			VerifierDigest:    frontend.Variable(0), // Can be empty for defining the circuit
			InputHash:         frontend.Variable(0),
			OutputHash:        frontend.Variable(0),
			CommonCircuitData: commonCircuitDataDummy,
		}

		verifierOnlyCircuitData := variables.DeserializeVerifierOnlyCircuitData(
			types.ReadVerifierOnlyCircuitData(circuitPath + "/verifier_only_circuit_data.json"),
		)
		proofWithPis := types.ReadProofWithPublicInputs(circuitPath + "/proof_with_public_inputs.json")
		inputHash, outputHash := GetInputHashOutputHash(proofWithPis)

		proofWithPisVariable := variables.DeserializeProofWithPublicInputs(proofWithPis)

		witness := Plonky2xVerifierCircuit{
			ProofWithPis:   proofWithPisVariable,
			VerifierData:   verifierOnlyCircuitData,
			VerifierDigest: verifierOnlyCircuitData.CircuitDigest,
			InputHash:      frontend.Variable(inputHash),
			OutputHash:     frontend.Variable(outputHash),
		}

		log := logger.Logger()

		log.Info().Msg("compiling verifier circuit")
		r1cs, pk, vk, err := CompileVerifierCircuit(circuitPath)
		if err != nil {
			log.Error().Msg("failed to compile verifier circuit:" + err.Error())
			os.Exit(1)
		}
		err = SaveVerifierCircuit(circuitPath, r1cs, pk, vk)
		if err != nil {
			log.Error().Msg("failed to save verifier circuit:" + err.Error())
			os.Exit(1)
		}

		log.Info().Msg("generating solidity contract")
		err = ExportIFunctionVerifierSolidity(circuitPath, vk)
		if err != nil {
			log.Error().Msg("failed to generate solidity contract:" + err.Error())
			os.Exit(1)
		}

		return test.IsSolved(&circuit, &witness, ecc.BN254.ScalarField())
	}

	assert.NoError(testCase(0))
}
