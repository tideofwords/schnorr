use anyhow::Result;

use plonky2::iop::{
    target::{BoolTarget, Target},
    witness::{PartialWitness, WitnessWrite},
};
use plonky2::field::{
    goldilocks_field::GoldilocksField,
    types::Field,
};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::{
    circuit_builder::CircuitBuilder,
    config::GenericConfig,
};

use crate::{
    mod65537::Mod65537Builder,
    schnorr::{SchnorrPublicKey, SchnorrSignature},
};

type GoldF = GoldilocksField;

pub struct MessageTarget {
    msg: Vec<Target>,
}

impl MessageTarget {
    fn new_with_size(builder: &mut CircuitBuilder<GoldF, 2>, n: usize) -> Self {
        Self {
            msg: builder.add_virtual_targets(n),
        }
    }

    fn set_witness(&self, pw: &mut PartialWitness<GoldF>, msg: &Vec<GoldF>) -> Result<()> {
        assert!(msg.len() == self.msg.len());
        for (&t, &x) in self.msg.iter().zip(msg.iter()) {
            pw.set_target(t, x)?;
        }

        Ok(())
    }
}

pub struct SchnorrSignatureTarget {
    s: Target,
    e: Target,
}

impl SchnorrSignatureTarget {
    fn new_virtual(builder: &mut CircuitBuilder<GoldF, 2>) -> Self {
        let s = builder.add_virtual_target();
        let e = builder.add_virtual_target();
        Self{ s, e }
    }

    fn set_witness(&self, pw: &mut PartialWitness<GoldF>, sig: &SchnorrSignature) -> Result<()> {
        pw.set_target(self.s, GoldilocksField::from_canonical_u64(sig.s))?;
        pw.set_target(self.e, GoldilocksField::from_canonical_u64(sig.e))?;
        Ok(())
    }
}

pub struct SchnorrPublicKeyTarget {
    pk: Target,
}

impl SchnorrPublicKeyTarget {
    fn new_virtual(builder: &mut CircuitBuilder<GoldF, 2>) -> Self {
        Self{ pk: builder.add_virtual_target() }
    }

    fn set_witness(&self, pw: &mut PartialWitness<GoldF>, pk: &SchnorrPublicKey) -> Result<()> {
        pw.set_target(self.pk, pk.pk)?;
        Ok(())
    }
}

pub struct SchnorrBuilder {}

impl SchnorrBuilder {
    pub fn constrain_sig <
        C: GenericConfig<2, F = GoldF>,
    > (
        &self,
        builder: &mut CircuitBuilder::<GoldF, 2>,
        sig: &SchnorrSignatureTarget,
        msg: &MessageTarget,
        pk: &SchnorrPublicKeyTarget,
    ) -> () {
        let verification_output = self.verify_sig::<C>(builder, sig, msg, pk);
        let true_target = builder._true();
        builder.connect(verification_output.target, true_target.target);
    }

    pub fn verify_sig <
        C: GenericConfig<2, F = GoldF>,
    > (
        &self,
        builder: &mut CircuitBuilder::<GoldF, 2>,
        sig: &SchnorrSignatureTarget,
        msg: &MessageTarget,
        pk: &SchnorrPublicKeyTarget,
    ) -> BoolTarget {
        let PRIME_GROUP_GEN: Target = builder.constant(GoldF::from_canonical_u64(6612579038192137166));
        let PRIME_GROUP_ORDER: Target = builder.constant(GoldF::from_canonical_u64(65537));
        const num_bits_exp: usize = 32;

        /* here's the direct verification calculation,
        which we verify in-circuit
        let r: GoldF = Self::pow(self.PRIME_GROUP_GEN, sig.s)
            * Self::pow(pk.pk, sig.e);
        let e_v: u64 = self.hash_insecure(&r, msg);
        e_v == sig.e   */

        let gs: Target = builder.exp(PRIME_GROUP_GEN, sig.s, num_bits_exp);
        let pe: Target = builder.exp(pk.pk, sig.e, num_bits_exp);
        let r: Target = builder.mul(gs, pe);

        // compute hash
        // note that it's safe to clone Targets since they just contain indices
        let hash_input: Vec<Target> = std::iter::once(r)
            .chain(msg.msg.iter().cloned()) 
            .collect();
        let hash_output: Target = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            hash_input,
        ).elements[0]; // whoops have to take mod group order;

        let e: Target = Mod65537Builder::mod_65537(builder, hash_output);

        // test equality
        builder.is_equal(e, sig.e)
    }
}

#[cfg(test)]
mod tests{
    use crate::schnorr::{SchnorrPublicKey, SchnorrSecretKey, SchnorrSigner, SchnorrSignature};
    use crate::schnorr_prover::{MessageTarget, SchnorrBuilder, SchnorrPublicKeyTarget, SchnorrSignatureTarget};
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::CircuitConfig,
        config::{GenericConfig, PoseidonGoldilocksConfig},
    };
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

        let pk_targ = SchnorrPublicKeyTarget::new_virtual(&mut builder);
        let sig_targ = SchnorrSignatureTarget::new_virtual(&mut builder);
        let msg_targ = MessageTarget::new_with_size(&mut builder, msg_size);

        
        // instead of verifying we're going to prove the verification
        sb.constrain_sig::<PoseidonGoldilocksConfig> (
            &mut builder,
            &sig_targ,
            &msg_targ,
            &pk_targ
        );

        // assign witnesses for verification
        let mut pw: PartialWitness<F> = PartialWitness::new();
        pk_targ.set_witness(&mut pw, &pk).unwrap();
        sig_targ.set_witness(&mut pw, &sig).unwrap();
        msg_targ.set_witness(&mut pw, &msg).unwrap();


        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
    }
}