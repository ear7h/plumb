use crate::tuple_macro;

pub trait TypeCons<T>{
    type Cons;

    fn cons(self, t : T) -> Self::Cons;
}

#[macro_export]
macro_rules! type_cons {
    ($x:path, $t:path) => {
        <$x as TypeCons<$t>>::Cons
    }
}

macro_rules! impl_type_cons {
    ($($x:ident,)*) => {
        impl<T, $($x,)*>TypeCons<T> for ($($x,)*) {
            type Cons = ($($x,)* T,);

            fn cons(self, t : T) -> Self::Cons {
                #![allow(non_snake_case)]
                let ($($x,)*) = self;
                ($($x,)* t,)
            }
        }
    }
}

tuple_macro!(impl_type_cons);


