import Lake
open Lake DSL

package ray where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4"
require interval from git "https://github.com/girving/interval"

@[default_target]
lean_lib Ray

@[default_target]
lean_exe gradient_test {
  root := `Ray.Render.GradientTest
  moreLinkArgs := #["-L/opt/homebrew/lib", "-lpng"]
}

@[default_target]
lean_exe bad_mandelbrot {
  root := `Ray.Render.BadMandelbrot
  moreLinkArgs := #["-L/opt/homebrew/lib", "-lpng"]
}

@[default_target]
lean_exe primes {
  root := `Ray.Experimental.Primes
}

target png.o pkg : FilePath := do
  let o := pkg.buildDir / "Ray/Render/png.o"
  let src ← inputFile <| pkg.dir / "Ray/Render/png.cc"
  let args := #["-I", (←getLeanIncludeDir).toString, "-I/opt/homebrew/include"]
  buildO o src args #["-fPIC"] "c++" getLeanTrace

extern_lib libray pkg := do
  let name := nameToStaticLib "ray"
  let png ← fetch <| pkg.target ``png.o
  buildStaticLib (pkg.nativeLibDir / name) #[png]

