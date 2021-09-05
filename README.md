# plumb

A pipeline framework

```rust
pub async fn test() -> Result<bool, f32> {
    async fn always_true(_a : i32, _b : i32, _s : &str) -> bool {
        true
    }

    id::<i32>()
    .bind(20 as i32)
    .bind("hello")
    .aseq(always_true)
    .tuple()
    .seq(|b : bool| {
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
    .run(12).await
}
```

**TODO:**
* documentation
* `map_err`
* `or_*` methods
* `iter_parallel`, `fold_parallel`

