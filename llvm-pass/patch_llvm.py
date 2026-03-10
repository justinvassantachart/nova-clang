import os
import sys
import re

llvm_dir = sys.argv[1]
pass_file = os.path.join(os.path.dirname(__file__), "NovaDebugPass.cpp")

# 1. Copy pass to LLVM Passes directory
dest_pass = os.path.join(llvm_dir, "llvm", "lib", "Passes", "NovaDebugPass.cpp")
with open(pass_file, 'r') as src, open(dest_pass, 'w') as dst:
    dst.write(src.read())

# 2. Add to CMakeLists.txt
cmake_file = os.path.join(llvm_dir, "llvm", "lib", "Passes", "CMakeLists.txt")
with open(cmake_file, 'r') as f:
    cmake = f.read()

if "NovaDebugPass.cpp" not in cmake:
    cmake = cmake.replace("PassBuilder.cpp", "PassBuilder.cpp\n  NovaDebugPass.cpp")
    with open(cmake_file, 'w') as f:
        f.write(cmake)

# 3. Hook into PassBuilder.cpp
pb_file = os.path.join(llvm_dir, "llvm", "lib", "Passes", "PassBuilder.cpp")
with open(pb_file, 'r') as f:
    pb = f.read()

# --- CACHE BUSTING: Clean up ALL previous broken ABI struct injections ---
pb = re.sub(r'#include "llvm/Passes/PassPlugin\.h"\nextern "C".*?llvmGetPassPluginInfo\(\);\n', '', pb)
pb = re.sub(r'\s*llvmGetPassPluginInfo\(\)\.RegisterPassBuilderCallbacks\(\*this\);.*?\n', '\n', pb)

if "injectNovaDebugPass" not in pb:
    # Inject Headers
    inc_target = '#include "llvm/Passes/PassBuilder.h"'
    inc_inject = inc_target + '\nextern void injectNovaDebugPass(llvm::PassBuilder &PB);\n'
    pb = pb.replace(inc_target, inc_inject)
    
    # Inject direct static C++ call (Immune to WebAssembly Plugin ABI Traps)
    constructor_idx = pb.find("PassBuilder::PassBuilder(")
    if constructor_idx == -1:
        print("FATAL: Could not find PassBuilder constructor!")
        sys.exit(1)
        
    brace_idx = pb.find("{", constructor_idx)
    injection = "\n  injectNovaDebugPass(*this); // NovaDebugPass statically linked safely\n"
    pb = pb[:brace_idx+1] + injection + pb[brace_idx+1:]
    
    with open(pb_file, 'w') as f:
        f.write(pb)

# FORCE CACHE INVALIDATION: Update modified time so ccache is forced to recompile
os.utime(pb_file, None)
os.utime(dest_pass, None)

print("NovaDebugPass successfully statically linked! (Cache Busted)")
