use anyhow::Result;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::types::Field;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::hash_types::RichField;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;

pub struct SchnorrSignatureTarget {
    s: Target,
    e: Target,
}

pub struct SchnorrPublicKeyTarget {
    pk: Target,
}

pub struct SchnorrBuilder {

}

impl SchnorrBuilder {
    // the output Target is constrained to equal x^a
    // here we assume that 

    // waaait, maybe I can use their built in thing
    fn prove_power<
        F: RichField + Extendable<D>, 
        C: GenericConfig<D, F = F>,
        const D: usize
    > (builder: &mut CircuitBuilder::<F, D>, x: Target, a: Target, num_bits: usize) -> Target {
        let bits: Vec<BoolTarget> = builder.split_le(a, num_bits);
        // make a sequence of targets x_i
        // where x_0 = 1
        // x_{num_bits} = x^a
        // and in between:
        // x_i = x_{i-1}**2 * (bits[num_bits+1-i] ? 1 : x)

    }

    fn constrain_sig <
        C: GenericConfig<2, F = GoldilocksField>,
    > (
        builder: &mut CircuitBuilder::<GoldilocksField, 2>,
        sig: &SchnorrSignatureTarget,
        msg: &Vec<Target>,
        pk: &SchnorrPublicKeyTarget,
    ) -> () {
        let PRIME_GROUP_GEN: Target = builder.constant(GoldilocksField::from_canonical_u64(6612579038192137166));
        const num_bits_exp: usize = 32;

        /*
        let r: GoldilocksField = Self::pow(self.PRIME_GROUP_GEN, sig.s)
            * Self::pow(pk.pk, sig.e);
        let e_v: u64 = self.hash_insecure(&r, msg);
        e_v == sig.e   */

        let gs: Target = builder.exp(PRIME_GROUP_GEN, sig.s, num_bits_exp);
        let pe: Target = builder.exp(pk.pk, sig.e, num_bits_exp);
        let r: Target = builder.mul(gs, pe);

        // compute hash
        let hash_input: Vec<Target> = std::iter::once(r)
            .chain(msg.iter().cloned())
            .collect();
        let e: Target = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            hash_input,
        ).elements[0];

        // verify equality
        builder.connect(e, sig.e);

    }
}