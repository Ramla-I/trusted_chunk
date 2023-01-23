# trusted_chunk
## Running Prusti on this crate
1. Download the pre-built binary for the latest release version
2. Navigate to the prusti-release folder
3. Run this command 
```
./prusti-rustc <path to trusted_chunk/src/lib.rs> -Pcheck_overflows=false --crate-type=lib --cfg "prusti"
```