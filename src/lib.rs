use std::pin::Pin;
use std::marker::PhantomData;
use std::future::Future;
use std::sync::Arc;

use tuple_utils::{Append, Call};

pub type PinBoxFut<T> = Pin<Box<dyn Future<Output = T> + Send>>;

macro_rules! assert_trait {
    ($tr:path, $val:expr) => {
        {
            if false {
                let _x : &dyn $tr = &$val;
                unreachable!();
            }

            $val
        }
    };
    ($tr:path, $val:expr,) => {
        {
            if false {
                let _x : &dyn $tr = &$val;
                unreachable!();
            }

            $val
        }
    }
}

pub trait Pipe {
    type Input;
    type Output;

    fn run(&self, input  : Self::Input) -> PinBoxFut<Self::Output>;
}

impl<T> PipeExt for T
where
    T : Pipe {}

pub trait ResultT {
    type Ok;
    type Err;

    fn into_result(self) -> Result<Self::Ok, Self::Err>;
}

#[macro_export]
macro_rules! result_ok {
    ($x:path) => {
        <$x as ResultT>::Ok
    }
}

#[macro_export]
macro_rules! result_err {
    ($x:path) => {
        <$x as ResultT>::Err
    }
}

impl<T, E> ResultT for Result<T, E> {
    type Ok = T;
    type Err = E;

    fn into_result(self) -> Result<T, E> {
        self
    }
}

pub trait PipeExt : Pipe {
    /// adds a `clone` of `T` to the current output
    fn bind<T>(self, t : T) -> Bind<Self, T>
    where
        Self : Sized,
        Self::Output : Append<T> + 'static,
        T : Send + Clone + 'static,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = <Self::Output as Append<T>>::Output,
            >,
            Bind{ s : self, t }
        }
    }

    /// A combination of `map` and `bind`; adds a clone of `t` to the
    /// result if it is `Ok`.
    ///
    /// Note: In order to clone `t` lazily, an `Arc` is used internally
    /// which gets cloned eagerly.
    fn map_bind<T>(self, t : T) -> MapBind<Self, T>
    where
        Self : Sized + 'static,
        Self::Output : ResultT,
        result_ok!(Self::Output) : Append<T>,
        T : Clone + Send + Sync + 'static,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = Result<
                    <result_ok!(Self::Output) as Append<T>>::Output,
                    result_err!(Self::Output),
                >,
            >,
            MapBind{s : self, t : Arc::new(t) }
        }
    }

    /// Puts the `Output` in a `tuple` such that it becomes part of the
    /// `TypeCons` and `TupleApply` traits.
    fn tuple(self) -> Tuple<Self>
    where
        Self : Sized,
        Self::Output : 'static,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = (Self::Output,)
            >,
            Tuple{s : self}
        }
    }

    /// A combination of `map` and `tuple`; if the result of the current
    /// computation is `Ok` then it gets put in a tuple.
    fn map_tuple(self) -> MapTuple<Self>
    where
        Self : Sized,
        Self::Output : ResultT + 'static,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = Result<
                    (<Self::Output as ResultT>::Ok,),
                    <Self::Output as ResultT>::Err,
                >
            >,
            MapTuple{s : self}
        }
    }

    /// Like `Result::and_then`, sequence an asynchronous computation that only
    /// runs when the current commputation returns an `Ok`
    fn aand_then<F, Fut, O>(self, f : F) -> AAndThen<Self, F, Fut>
    where
        Self : Sized,
        Self::Output : ResultT + 'static,
        result_err!(Self::Output) : Send,
        F : Call<result_ok!(Self::Output), Fut> + Clone + Send + 'static,
        Fut : Future + Send,
        Fut::Output : ResultT<Ok = O, Err = result_err!(Self::Output)>,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = Result<O, result_err!(Self::Output)>,
            >,
            AAndThen{s : self, f, _marker : Default::default() }
        }

    }

    /// Like `Result::and_then`, sequence a synchronous computation that only
    /// runs when the current commputation returns an `Ok`
    fn and_then<F, OOk>(self, f : F) -> AndThen<
        Self,
        F,
        Result<OOk, result_err!(Self::Output)>
    >
    where
        Self : Sized,
        Self::Output : ResultT + 'static,
        F : Call<
            result_ok!(Self::Output),
            Result<OOk, result_err!(Self::Output)>
        > + Send + Sync + Clone + 'static,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = Result<OOk, result_err!(Self::Output)>
            >,
            AndThen{s : self, f, _marker : Default::default()}
        }
    }


    /// Like `Result::map`, sequence an asynchronous computation that only runs
    /// when the current commputation returns an `Ok`
    fn amap<F, Fut, O>(self, f : F) -> AMap<Self, F, Fut>
    where
        Self : Sized,
        Self::Output : ResultT + Send + 'static,
        result_ok!(Self::Output) : Send,
        result_err!(Self::Output) : Send,
        F : Call<
            result_ok!(Self::Output),
            Fut,
        > + Clone + Send + 'static,
        Fut : Future<Output = O> + Send,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = Result<O, <Self::Output as ResultT>::Err>,
            >,
            AMap{s : self, f, _marker : Default::default() }
        }

    }

    /// Like `Result::map`, sequence a synchronous computation that only runs
    /// when the current commputation returns an `Ok`
    fn map<F, O>(self, f : F) -> Map<Self, F, O>
    where
        Self : Sized,
        Self::Output : ResultT + 'static,
        F : Call<
            result_ok!(Self::Output),
            O
        > + Send + Sync + Clone + 'static,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = Result<O, <Self::Output as ResultT>::Err>,
            >,
            Map{s : self, f, _marker : Default::default()}
        }
    }

    /// A convenience function equivalent to calling
    /// `aseq` then `tuple`
    fn aseqt<F, Fut, O>(self, f : F) -> Tuple<ASeq<Self, F, Fut>>
    where
        Self : Sized,
        Self::Output : Send + 'static,
        O : 'static,
        Fut : Future<Output = O> + Send,
        F : Call<Self::Output, Fut> + Send + Clone + 'static,
    {
        assert_trait!{
            Pipe<
                Input = Self::Input,
                Output = (O,)
            >,
            Tuple{
                s : ASeq{s : self, f, _marker : Default::default()}
            }
        }
    }

    /// Sequence the current computation with an asynchronous one
    fn aseq<F, Fut, O>(self, f : F) -> ASeq<Self, F, Fut>
    where
        Self : Sized,
        Self::Output : Send + 'static,
        F : Call<Self::Output, Fut> + Send + Clone + 'static,
        Fut : Future<Output = O> + Send,
    {
        assert_trait!{
            Pipe<Input = Self::Input, Output = O>,
            ASeq{s : self, f, _marker : Default::default()}
        }
    }

    /// A convenience function equivalent to calling
    /// `seq` then `tuple`
    fn seqt<F, O>(self, f : F) -> Tuple<Seq<Self, F, O>>
    where
        Self : Sized,
        Self::Output : 'static,
        O : 'static,
        F : Call<Self::Output, O> + Send + Clone + 'static,
    {
        assert_trait!{
            Pipe<Input = Self::Input, Output = (O,)>,
            Tuple{
                s : Seq{s : self, f, _marker : Default::default()}
            }
        }
    }

    /// Sequence the current computatation with a synchronous one
    fn seq<F, O>(self, f : F) -> Seq<Self, F, O>
    where
        Self : Sized,
        Self::Output : 'static,
        F : Call<Self::Output, O> + Send + Clone + 'static,
    {
        assert_trait!{
            Pipe<Input = Self::Input, Output = O>,
            Seq{s : self, f, _marker : Default::default()}
        }
    }
}

/// Arc is used to clone the inner type lazily. First the Arc gets cloned
/// so the inner T can be reachable in an async move block (as opposed to
/// reference captured in a normal async block, which makes them ?Send).
/// Then, S is run and the inner T is cloned iff the result is ok.
#[derive(Clone)]
pub struct MapBind<S, T> {
    s : S,
    t : Arc<T>,
}

impl<S, T> Pipe for MapBind<S, T>
where
    S : Pipe + 'static,
    S::Output : ResultT,
    result_ok!(S::Output) : Append<T>,
    T : Send + Sync + Clone + 'static,
{
    type Input = S::Input;
    type Output = Result<
        <result_ok!(S::Output) as Append<T>>::Output,
        <S::Output as ResultT>::Err,
    >;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);
        let arc = Arc::clone(&self.t);

        Box::pin(async move {
            fut.await.into_result().map(|x| x.append((*arc).clone()))
        })
    }
}

#[derive(Copy,Clone)]
pub struct MapTuple<S> {
    s : S,
}

impl<S> Pipe for MapTuple<S>
where
    S : Pipe,
    S::Output : ResultT + 'static,
{
    type Input = S::Input;
    type Output = Result<
            (<S::Output as ResultT>::Ok,),
            <S::Output as ResultT>::Err,
        >;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);

        Box::pin(async move {
            fut.await.into_result().map(|v| (v,))
        })
    }
}

#[derive(Copy,Clone)]
pub struct Tuple<S> {
    s : S,
}

impl<S> Pipe for Tuple<S>
where
    S : Pipe,
    S::Output : 'static,
{
    type Input = S::Input;
    type Output = (S::Output,);

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);

        Box::pin(async move {
            (fut.await,)
        })
    }
}

#[derive(Copy,Clone)]
pub struct AAndThen<S, F, Fut> {
    s : S,
    f : F,
    _marker : PhantomData<fn () -> Fut>,
}

impl<S, F, Fut> Pipe for AAndThen<S, F, Fut>
where
    S : Pipe,
    S::Output : ResultT + 'static,
    result_err!(S::Output) : Send,
    F : Call<result_ok!(S::Output), Fut> + Clone + Send + 'static,
    Fut : Future + Send,
    Fut::Output : ResultT<Err = result_err!(S::Output)>,
{
    type Input = S::Input;
    type Output = Result<result_ok!(Fut::Output), result_err!(S::Output)>;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);
        let next = self.f.clone();

        Box::pin(async move {

            let res : Result<_, _> = fut.await.into_result()
            .map(|v| {
                Call::call(next, v)
            });

            match res {
                Ok(fut) => fut.await.into_result(),
                Err(err) => Err(err),
            }
        })
    }
}

#[derive(Copy,Clone)]
pub struct AMap<S, F, Fut> {
    s : S,
    f : F,
    _marker : PhantomData<fn () -> Fut>,
}

impl<S, F, Fut> Pipe for AMap<S, F, Fut>
where
    S : Pipe,
    S::Output : ResultT + Send + 'static,
    result_ok!(S::Output) : Send,
    result_err!(S::Output) : Send,
    F : Call<
        result_ok!(S::Output),
        Fut
    > + Clone + Send + 'static,
    Fut : Future + Send,
{
    type Input = S::Input;
    type Output = Result<Fut::Output, <S::Output as ResultT>::Err>;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);
        let next = self.f.clone();

        Box::pin(async move {

            match fut.await.into_result() {
                Ok(v) => Ok(Call::call(next, v).await),
                Err(e) => Err(e),
            }

        })
    }
}

#[derive(Copy,Clone)]
pub struct AndThen<S, F, O> {
    s : S,
    f : F,
    _marker : PhantomData<fn () -> O>,
}

impl<S, F, OOk> Pipe for AndThen<S, F, Result<OOk, result_err!(S::Output)>>
where
    S : Pipe,
    S::Output : ResultT + 'static,
    F : Call<
        result_ok!(S::Output),
        Result<OOk, result_err!(S::Output)>
    > + Send + Sync + Clone + 'static,
{
    type Input = S::Input;
    type Output = Result<OOk, result_err!(S::Output)>;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);
        let f = self.f.clone();

        Box::pin(async move {
            fut.await.into_result().and_then(|v| {
                Call::call(f, v)
            })
        })
    }
}

#[derive(Copy,Clone)]
pub struct Map<S, F, O> {
    s : S,
    f : F,
    _marker : PhantomData<fn () -> O>,
}

impl<S, F, O> Pipe for Map<S, F, O>
where
    S : Pipe,
    S::Output : ResultT + 'static,
    F : Call<
        result_ok!(S::Output),
        O
    > + Send + Sync + Clone + 'static,
{
    type Input = S::Input;
    type Output = Result<O, result_err!(S::Output)>;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);
        let f = self.f.clone();

        Box::pin(async move {
            fut.await.into_result().map(|v| {
                Call::call(f, v)
            })
        })
    }
}


#[derive(Copy,Clone)]
pub struct Seq<S, F, O> {
    s : S,
    f : F,
    _marker : PhantomData<fn () -> O>,
}

impl<S, F, O> Pipe for Seq<S, F, O>
where
    S : Pipe,
    S::Output : 'static,
    F : Call<S::Output, O> + Send + Clone + 'static,
{
    type Input = S::Input;
    type Output = O;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);
        let f = self.f.clone();
        Box::pin(async move {
            Call::call(f, fut.await)
        })
    }
}


#[derive(Copy,Clone)]
pub struct Bind<S, T> {
    s : S,
    t : T,
}

impl<S, T> Pipe for Bind<S, T>
where
    S : Pipe,
    S::Output : Append<T> + 'static,
    T : Send + Clone + 'static,
{
    type Input = S::Input;
    type Output = <S::Output as Append<T>>::Output;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);
        let t = self.t.clone();
        Box::pin(async move {
            fut.await.append(t)
        })
    }
}


pub fn id<T>() -> Id<T> {
    Id{
        _marker : Default::default(),
    }
}

#[derive(Copy,Clone)]
pub struct Id<T>{
    _marker : PhantomData<T>,
}

impl<T> Pipe for Id<T>
where
    T : Send + 'static
{
    type Input = T;
    type Output = T;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        Box::pin(async move {
            i
        })
    }
}

#[derive(Copy,Clone)]
pub struct ASeq<S, F, Fut>{
    s : S,
    f : F,
    _marker : PhantomData<fn () -> Fut>,
}


impl<S, F, Fut> Pipe for ASeq<S, F, Fut>
where
    S : Pipe,
    S::Output : Send + 'static,
    F : Call<S::Output, Fut> + Send + Clone + 'static,
    Fut : Future + Send,
{

    type Input = S::Input;
    type Output = Fut::Output;

    fn run(&self, i : Self::Input) -> PinBoxFut<Self::Output> {
        let fut = self.s.run(i);
        let next = self.f.clone();

        Box::pin(async move {
            let j = fut.await;
            Call::call(next, j).await
        })
    }
}

pub async fn test() -> Result<bool, f32> {
    async fn always_true(_a : i32, _b : i32, _s : &str) -> bool {
        true
    }

    id::<i32>()
    .tuple()
    .bind(20 as i32)
    .bind("hello")
    .aseq(always_true)
    .tuple()
    .tuple().seq(|t : (_,)| {
        t.append(1.1)
    })
    .tuple().seq(|t : (_,_)| {
        t.append("hello")
    })
    .seq(|b : bool, _f : f32, _s : &str| {
        Ok((!b,))
    })
    .map(|b:bool| {
        !b
    })
    .map_tuple()
    .map_bind("abc")
    .amap(|_b:bool, _s : &str| async {
        false
    })
    .map_tuple()
    .and_then(|_| {
        Err(1.1)
    })
    .aand_then(|_ : f32| async {
        Err(1.2)
    })
    .run(12).await
}


