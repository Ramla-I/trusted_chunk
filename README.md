# trusted_chunk
## Running Prusti on this crate
1. Download the pre-built binary for the latest release version
2. You may have to install the required toolchain for this Prusti release
3. Navigate to the prusti-release folder
4. Set all binary files in the prusti-release folder to executable
5. Run this command 
```
./prusti-rustc <path to trusted_chunk/src/lib.rs> -Pcheck_overflows=false --crate-type=lib --cfg "prusti"
```