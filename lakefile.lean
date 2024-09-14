import Lake
open Lake DSL

package ray where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "master"
require "girving" / "interval" @ git "main"

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
  let src ← inputTextFile <| pkg.dir / "Ray/Render/png.cc"
  let args := #["-I", (←getLeanIncludeDir).toString, "-I/opt/homebrew/include"]
  buildO o src args #["-fPIC"] "c++" getLeanTrace

extern_lib libray pkg := do
  let name := nameToStaticLib "ray"
  let png ← fetch <| pkg.target ``png.o
  buildStaticLib (pkg.nativeLibDir / name) #[png]
