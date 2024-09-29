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

pub struct MessageTarget {
    msg: Vec<Target>,
}

impl MessageTarget {
    fn new_with_size(builder: &mut CircuitBuilder<GoldilocksField, 2>, n: usize) -> Self {
        Self {
            msg: builder.add_virtual_targets(n),
        }
    }
}

pub struct SchnorrSignatureTarget {
    s: Target,
    e: Target,
}

impl SchnorrSignatureTarget {
    fn new_virtual(builder: &mut CircuitBuilder<GoldilocksField, 2>) -> Self {
        let s = builder.add_virtual_target();
        let e = builder.add_virtual_target();
        Self{ s, e }
    }
}

pub struct SchnorrPublicKeyTarget {
    pk: Target,
}

#[derive(Debug, Default)]
pub struct Mod65537Generator {
    a: Target,
    q: Target,
    r: Target,
}

pub struct SchnorrBuilder {

}

impl SchnorrBuilder {
    // Reduce a modulo the constant 65537
    // where a is the canonical representative for an element of the field
    // (meaning: 0 \leq a < p)

    // To verify this, write
    // a = 65537 * q + r, and do range checks to check that:
    // 0 <= q <= floor(p / 65537)
    // 0 <= r < 65537
    // (these first two checks guarantee that a lies in the range [0, p + 65536])
    // if q = floor(p / 65537) then r = 0
    // (note that p % 65537 == 1 so this is the only possibility)
    fn mod_65537 <
        C: GenericConfig<2, F = GoldilocksField>,
    > (
        builder: &mut CircuitBuilder::<GoldilocksField, 2>,
        a: &Target,
    ) -> Target {
        let q = builder.add_virtual_target();
        let r = builder.add_virtual_target();

        // the Mod65537Generator will assign values to q and r later
        builder.add_simple_generator( Mod65537Generator { a, q, r } );

        // impose four constraints
        // 1. a = 65537 * q + r
        let t65537 = builder.constant(GoldilocksField::from_canonical_u64(65537));
        let a_copy = builder.mul_add(t65537, q, r);
        builder.connect(*a, a_copy);

        // 2. 0 <= q <= floor(p / 65537)
        // max_q is 281470681743360 = floor(p / 65537) = (p-1) / 65537 = 2^48 - 2^32
        let max_q = builder.constant(GoldilocksField::from_canonical_u64(281470681743360));
        builder.range_check(q, 48);
        builder.range_check(builder.sub(max_q, q), 48);

        // 3. 0 <= r < 65537
        let max_r = builder.constant(GoldilocksField::from_canonical_u64(65537));
        builder.range_check(r, 17);
        builder.range_check(builder.sub(max_r, r), 17);

        // 4. if q = floor(p / 65537) then r = 0
        let q_equals_max = builder.is_equal(q, max_q);
        builder.connect(builder.mul(q_equals_max.target, r), builder.zero());

        r
    }

    fn constrain_sig <
        C: GenericConfig<2, F = GoldilocksField>,
    > (
        &self,
        builder: &mut CircuitBuilder::<GoldilocksField, 2>,
        sig: &SchnorrSignatureTarget,
        msg: &MessageTarget,
        pk: &SchnorrPublicKeyTarget,
    ) -> () {
        let PRIME_GROUP_GEN: Target = builder.constant(GoldilocksField::from_canonical_u64(6612579038192137166));
        let PRIME_GROUP_ORDER: Target = builder.constant(GoldilocksField::from_canonical_u64(65537));
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
        // note that it's safe to clone Targets since they just contain indices
        let hash_input: Vec<Target> = std::iter::once(r)
            .chain(msg.iter().cloned()) 
            .collect();
        let e: Target = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            hash_input,
        ).elements[0] // whoops have to take mod group order;

        // enforce equality
        builder.connect(e, sig.e);
    }
}

#[cfg(test)]
mod tests{
    use crate::schnorr::{SchnorrPublicKey, SchnorrSecretKey, SchnorrSigner, SchnorrSignature};
    use crate::schnorr_prover::SchnorrBuilder;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitData, VerifierOnlyCircuitData};
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::field::goldilocks_field::GoldilocksField;
    use rand;

    #[test]
    fn test_schnorr() -> () {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut rng: rand::rngs::ThreadRng = rand::thread_rng();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        builder.add_virtual_fri_proof(num_leaves_per_oracle, params)

        let sb: SchnorrBuilder = SchnorrBuilder{};

        // create keypair, message, signature
        let sk: SchnorrSecretKey = SchnorrSecretKey{ sk: 133 };
        let ss = SchnorrSigner::new();
        let pk: SchnorrPublicKey = ss.keygen(&sk);
        let msg: Vec<GoldilocksField> = ss.u64_into_goldilocks_vec(
            vec![1500, 1600, 0, 0, 0]
        );
        let msg_size: usize = msg.len();
        let sig: SchnorrSignature = ss.sign(&msg, &sk, &mut rng);

        let sig_target = builder.constant(sig);
        // instead of verifying we're going to prove the verification
        sb.constrain_sig(
            &mut builder,
            &sig,
            &msg,
            &pk
        );
    }
}