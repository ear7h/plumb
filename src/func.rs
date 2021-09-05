use std::marker::PhantomData;

use crate::tuple_macro;

pub struct Func<F, I, O> {
    pub f : F,
    _marker : PhantomData<fn (I) -> O>,
}

macro_rules! impl_from_closure_func {
    ($($x:ident,)*) => {

        impl<F, $($x,)* O> From<F> for Func<F, ($($x,)*), O>
        where
            F : Fn($($x,)*) -> O
        {
            fn from(f : F) -> Self {
                Func{
                    f,
                    _marker : Default::default(),
                }
            }
        }
    }
}

tuple_macro!(impl_from_closure_func);


pub trait TupleApply {
    type Output;

    fn apply(self) -> Self::Output;
}

pub fn apply_tuple<F, I, O>(f : F, i : I) -> O
where
    F : Into<Func<F, I, O>>,
    (Func<F, I, O>, I) : TupleApply<Output = O>
{
    let f : Func<_, _, _> = f.into();

    (f, i).apply()
}

macro_rules! impl_tuple_apply {
    ($($x:ident,)*) => {

        impl<F, $($x,)* O> TupleApply for
            (
                Func<F, ($($x,)*), O>,
                ($($x,)*)
            )
        where
            F : Fn($($x,)*) -> O
        {
            type Output = O;

            fn apply(self) -> Self::Output {
                #![allow(non_snake_case)]
                let ($($x,)*) = self.1;
                (self.0.f)($($x,)*)
            }
        }

    }
}

tuple_macro!(impl_tuple_apply);
