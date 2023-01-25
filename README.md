# trusted_chunk
## Running Prusti on this crate
1. Download the pre-compiled binary for Release v-2022-10-05-0726 from [here](https://github.com/viperproject/prusti-dev/releases/tag/v-2022-10-05-0726)
2. Navigate to the prusti-release folder
3. Run this command 
```
./prusti-rustc <path to trusted_chunk/src/lib.rs> -Pcheck_overflows=false --crate-type=lib --cfg "prusti"
```

## Notes for Prusti improvements
1. Eq, PartialEq, Ord, etc. traits should be pure by default