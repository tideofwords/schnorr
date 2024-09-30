use anyhow::Result;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, PartitionWitness, Witness, WitnessWrite};
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::hash_types::RichField;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::util::serialization::{Buffer, IoResult, Read, Write};

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

impl SimpleGenerator<GoldF, 2> for Mod65537Generator {
    fn id(&self) -> String {
        "Mod65537Generator".to_string()
    }
    fn dependencies(&self) -> Vec<Target> {
        vec![self.a]
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<GoldF>,
        out_buffer: &mut GeneratedValues<GoldF>,
    ) -> Result<()> {
        let a = witness.get_target(self.a);
        let a64 = a.to_canonical_u64();
        let q64 = a64 / 65537;
        let r64 = a64 % 65537;

        out_buffer.set_target(self.q, GoldF::from_canonical_u64(q64));
        out_buffer.set_target(self.r, GoldF::from_canonical_u64(r64));

        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, common_data: &CommonCircuitData<GoldF, 2>) -> IoResult<()> {
        println!("SERIALIZATION!  What is this good for?");
        dst.write_target(self.a)?;
        dst.write_target(self.q)?;
        dst.write_target(self.r)?;
        Ok(())
    }

    fn deserialize(src: &mut Buffer, common_data: &CommonCircuitData<GoldF, 2>) -> IoResult<Self>
    where
        Self: Sized 
    {
            println!("DESERIALIZATION!  What is this good for?");
            let a = src.read_target()?;
            let q = src.read_target()?;
            let r = src.read_target()?;
            Ok(Self { a, q, r })
    }
}

pub struct SchnorrBuilder {}

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
    pub(crate) fn mod_65537 <
        //C: GenericConfig<2, F = GoldF>,
    > (
        builder: &mut CircuitBuilder::<GoldF, 2>,
        a: Target,
    ) -> Target {
        let q = builder.add_virtual_target();
        let r = builder.add_virtual_target();

        // the Mod65537Generator will assign values to q and r later
        builder.add_simple_generator( Mod65537Generator { a, q, r } );

        // impose four constraints
        // 1. a = 65537 * q + r
        let t65537 = builder.constant(GoldF::from_canonical_u64(65537));
        let a_copy = builder.mul_add(t65537, q, r);
        builder.connect(a, a_copy);

        // 2. 0 <= q <= floor(p / 65537)
        // max_q is 281470681743360 = floor(p / 65537) = (p-1) / 65537 = 2^48 - 2^32
        let max_q = builder.constant(GoldF::from_canonical_u64(281470681743360));
        builder.range_check(q, 48);
        let diff_q = builder.sub(max_q, q);
        builder.range_check(diff_q, 48);

        // 3. 0 <= r < 65537
        let max_r = builder.constant(GoldF::from_canonical_u64(65537));
        builder.range_check(r, 17);
        let diff_r = builder.sub(max_r, r);
        builder.range_check(diff_r, 17);

        // 4. if q = floor(p / 65537) then r = 0
        let q_equals_max = builder.is_equal(q, max_q);
        let prod_temp = builder.mul(q_equals_max.target, r);
        let zero_temp = builder.zero();
        builder.connect(prod_temp, zero_temp);

        // throw in the Generator to tell builder how to compute r
        builder.add_simple_generator( Mod65537Generator {a, q, r} );

        r
    }

    pub fn constrain_sig <
        C: GenericConfig<2, F = GoldF>,
    > (
        &self,
        builder: &mut CircuitBuilder::<GoldF, 2>,
        sig: &SchnorrSignatureTarget,
        msg: &MessageTarget,
        pk: &SchnorrPublicKeyTarget,
    ) -> () {
        println!("WARNING constrain_sig() is not done yet DONT USE IT");

        let PRIME_GROUP_GEN: Target = builder.constant(GoldF::from_canonical_u64(6612579038192137166));
        let PRIME_GROUP_ORDER: Target = builder.constant(GoldF::from_canonical_u64(65537));
        const num_bits_exp: usize = 32;

        /*
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
        let e: Target = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            hash_input,
        ).elements[0]; // whoops have to take mod group order;

        // enforce equality
        builder.connect(e, sig.e);
    }
}

#[cfg(test)]
mod tests{
    use crate::schnorr::{SchnorrPublicKey, SchnorrSecretKey, SchnorrSigner, SchnorrSignature};
    use crate::schnorr_prover::SchnorrBuilder;
    use plonky2::iop::target::Target;
    use plonky2::iop::witness::{PartialWitness, PartitionWitness, Witness, WitnessWrite};
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitData, VerifierOnlyCircuitData};
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::Field;
    use rand;

    #[test]
    fn test_mod65537() -> () {
        const D: usize = 2;
        const p: u64 = 18446744069414584321;  // the Goldilocks prime
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a: Vec<Target> = vec![0, 1, 2, 65535, 65536, 65537, p - 4, p - 3, p - 2, p - 1]
            .into_iter()
            .map(|x| builder.constant(GoldilocksField::from_canonical_u64(x)))
            .collect();

        //let r0 = SchnorrBuilder::mod_65537(&mut builder, &a[0]);

        let r: Vec<Target> = a.iter()
            .map(|targ| SchnorrBuilder::mod_65537(&mut builder, *targ))
            .collect();

        builder.register_public_inputs(&a);
        
        let mut pw: PartialWitness<F> = PartialWitness::new();
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        // introspect to check the values of stuff

        ()
    }

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
/* 
        let sig_target = builder.constant(sig);
        // instead of verifying we're going to prove the verification
        sb.constrain_sig(
            &mut builder,
            &sig,
            &msg,
            &pk
        ); */
    }
}