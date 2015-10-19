#!/bin/bash

#;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
# __author__ = "Kurt Pagani <nilqed@gmail.com>"
# __svn_id__ = "$Id: setup 1 2015-10-17 23:14:11Z pagani $"
#;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#
# iSPAD Installation  
# ==================
# 1. Check FriCAS installation
# 2. Find AxiomSYS
# 3. Check SBCL installation
# 3.1 SBCL_HOME
# 3.2 SBCL Executable
# 3.3 SBCL/QuickLisp dependencies
# 4. Checking Jupyter installation
# 5. Creating iSPAD core from AxiomSYS
# 6. Generate and install kernel spec
# 7. Install iSPAD binary
#;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

# Install iSPAD to ...
install_dir="$HOME/.local/bin"

# Messages
fricas_in_path="FriCAS in path ... ok."
fricas_not_in_path="[1] FriCAS not found ... exit."
axiomsys_found="AxiomSYS found ... ok."
axiomsys_not_found="[2] AxiomSYS not found ... exit."
sbcl_home_defined="SBCL_HOME set ... ok."
sbcl_home_not_def="[3] SBCL_HOME not set. exit."
sbcl_exe_found="SBCL executable ... ok."
sbcl_exe_not_found="[4] SBCL executable not found ... exit."
ql_dep_ok="SBCL/QuickLisp ......... ok."
ql_dep_failed="[5] SBCL/QuickLisp failed ... exit."
ispad_core_ok="iSPAD core built ... ok."
ispad_core_failed="[6] Building iSPAD core failed ... exit."
jupyter_ok="Jupyter command ... ok."
jupyter_not_found="[7] Jupyter command not found ... exit."
kernel_spec_ok="Kernel spec installed ... ok."
kernel_spec_failed="[8] Installation of kernel spec failed ... exit."
install_ispad_ok="Executable iSPAD installed ... ok."
install_ispad_failed="[9] Installation of iSPAD failed ... exit."
id_created="Installation directory created ... ok."

# Banner
echo =================================================
echo Installation of iSPAD - Jupyter kernel for FriCAS 
echo =================================================

# Check if FriCAS in path
echo ------------------
echo FriCAS installed ?
echo ------------------

if fricas -nogo; then 
    echo $fricas_in_path ; 
else 
    echo $fricas_not_in_path ; 
    exit 1 ;
fi 

# Find AxiomSYS 
echo ---------------
echo AxiomSYS path ?
echo ---------------

export AXSYS="?"
if fricas -nogo > axsys ; then
    export AXSYS=$(awk '/-ws/ {print $(NF)}' axsys);
    rm axsys ;
fi

if [ ! -f  "$AXSYS" ] ; then
    echo $axiomsys_not_found ;
    exit 1 ;
else
    echo $axiomsys_found ;
    echo $AXSYS ;
    export AXIOM=$(dirname $(dirname $AXSYS)) ;
fi

# Check SBCL installation
echo ----------------
echo SBCL installed ?
echo ----------------

if [ -d "$SBCL_HOME" ] ; then
    echo $sbcl_home_defined ;
    echo $SBCL_HOME ;
else
    echo $sbcl_home_not_def ;
    exit 1 ;
fi


echo -----------------
echo SBCL executable ?
echo -----------------

if !(sbcl --version) ; then
    echo $sbcl_exe_not_found ;  
    exit 1 ;
else
    echo $sbcl_exe_found ;
fi

# QuickLisp 
echo -------------------------------------------
echo SBCL/QuickLisp dependencies ... pre-loading
echo -------------------------------------------

if sbcl --non-interactive --load "lisp/quick.lisp" ; then
    echo $ql_dep_ok ; 
else
    echo $ql_dep_failed ; 
    exit 1 ;
fi 

# Checking Jupyter
echo ---------------------------------
echo Checking Jupyter installation ...
echo ---------------------------------

if !(jupyter --version) ; then
    echo $jupyter_not_found ;
    exit 1
else
    jupyter --paths ;
    echo $jupyter_ok ;
fi



# Creating the iSPAD image

echo -------------------------------------
echo Creating iSPAD core from AxiomSYS ...
echo -------------------------------------

if [ -f  $AXSYS ] ; then
    echo ")lisp (load \"lisp/sbcl.lisp\")" > acmd
	sbcl --core  $AXSYS < acmd;
	rm acmd;
fi

if [ -x "iSPAD" ] ; then
    echo $ispad_core_ok ;
else
    echo $ispad_core_failed ;
    exit 1 ;
fi


# Install kernel spec
echo ----------------------------------------
echo Install Jupyer Kernel Spec : kernel.json
echo ----------------------------------------

mkdir ./ifricas
kspec=./ifricas/kernel.json

echo '{"argv": ['"\"$install_dir/iSPAD\""',"{connection_file}"],' > $kspec
echo '"codemirror_mode": "shell",' >> $kspec
echo '"display_name": "FriCAS",' >> $kspec
echo '"language": "spad"}' >> $kspec
echo kernel.json written to $kspec
echo



if jupyter kernelspec install --user ./ifricas ; then
    jupyter kernelspec list ;
    echo $kernel_spec_ok ; 
else
    echo $kernel_spec_failed ; 
    exit 1 ;
fi 


# Install iSPAD binary
echo -----------------------
echo Installing iSPAD binary 
echo -----------------------

if [ ! -d "$install_dir" ]; then
    mkdir $install_dir ;
    echo $id_created ;
fi

if cp -v ./iSPAD $install_dir ; then
    echo $install_ispad_ok ;
else
    echo $install_ispad_failed ;
    exit 1
fi


# Congratulations
echo ------------------------------------
echo "*** iSPAD successfully installed ***" 
echo ------------------------------------
echo To use the kernel do as follows:
echo "    $ jupyter notebook" 
echo "    goto: http://localhost:8888"
echo "    choose: New -> FriCAS"
echo ====================================

