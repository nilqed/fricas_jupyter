## fricas_jupyter

Jupyter kernel for [FriCAS](http://fricas.sourceforge.net/) based on
Frederic Peschanski's [cl-jupyter](https://github.com/fredokun/cl-jupyter).


#### Prerequisites

* [FriCAS](http://fricas.sourceforge.net/) installed, SBCL version 
* [SBCL 1.2.x](http://www.sbcl.org/) for Linux, `SBCL_HOME` set!
* [Jupyter 4.1+](https://jupyter.org/), check with `$jupyter --paths`

**Note**: The version of SBCL must match that of which FriCAS has been compiled!
This is so because SBCL cannot load cores (AxiomSYS in this case) of different
versions. See `FAQ` (further below) how to get type/version of FriCAS' 
underlying Lisp. By the way there will be no harm to your existing FriCAS 
installation ;)    

Tested on Ubuntu 14+. If you are missing some of the items above then consult the
links given to get installation information. The `install.sh` script
is going to check all the prerequisites and will `exit` in case of missing items,
thereby issuing an error number `[n]` which might help to fix (see below).

#### Installation

##### Get the sources

Either by `git`: 

    git clone https://github.com/nilqed/fricas_jupyter.git
 
or by downloading a `zip` file: 
[master](https://github.com/nilqed/fricas_jupyter/archive/master.zip).
Unpack with

    unzip fricas_jupyter-master.zip
    
    
##### Build & Install 

Change to the source directory and run the install script:

    ./install.sh
    

    
##### Test

    jupyter notebook 
    http://localhost:8888
      New -> FriCAS
      


#### Error Codes
If you encounter an error (marked by a number in square brackets at a line begin)
then check the corresponding hints below to resolve the issue.
                 
    [1] ... Check $PATH and/or try: $ fricas -list
    [2] ... Check if AxiomSYS is in $AXIOM/bin       
    [3] ... Set SBCL_HOME. Check with $echo $SBCL_HOME
    [4] ... Check $PATH and/or try: $ sbcl --version
    [5] ... Retry ./install.sh
    [6] ... Retry ./install.sh
    [7] ... Check manually with: $jupyter --paths
    [8] ... Try: $jupyter kernelspec install --user ./ifricas 
    [9] ... Check if $HOME/.local/bin exists and is writable.

    
If the hints above do not help then open an issue
[here](https://github.com/nilqed/fricas_jupyter/issues), please. 
A log file generated by `./install.sh > install.log` might be useful.


#### Remarks

There are only two files to be installed by `install.sh`:

    ifricas/kernel.json -> $HOME/.local/share/jupyter/kernels
    
    iSPAD -> $HOME/.local/bin
    
Those can easily be removed by hand (no sudo required). 

The first time the **Lisp** sources will be compiled by `quickload`, usually to
a cache like:

    $HOME/.cache/common-lisp/sbcl-1.2.14-linux-x64/...
   

and this may take some minutes. 
Subsequent `installs` (e.g. after upgrading Lisp files) will use the cache, what is
much faster. 

However, afer a successful installation the source directory will not be used anymore 
and can be deleted (if wished so).

---
#### FAQ

1. How to check which Common-Lisp flavour/version was used to build FriCAS?
    ```
    fricas -nox 
     )lisp (lisp-implementation-type)
     )lisp (lisp-implementation-version)
     )quit
    ```
    
2. How to interrupt/continue the kernel?
    ```
    To interrupt use the notebook menu entry: Kernel/Interrupt
    To continue type '0' in the console (debugger continue)
    ```

3. How to use `*debugger-hook*` ?
    ```
    Enter the following in two separate cells of the notebook:
    
    )lisp (defun debug-ignore (c h) (declare (ignore h)) (print c) (abort))
    )lisp (setf *debugger-hook* #'debug-ignore)
    
    After that, any 'interrupt' only shows a message and ignores the debugger.
    ```

#### Docker (automated build)
There is a docker image at https://hub.docker.com/r/nilqed/fricas_jupyter/


    docker pull nilqed/fricas_jupyter
    docker run -p 443:8888  -t -i nilqed/fricas_jupyter jupyter notebook
    go to http://localhost:443
    New -> FriCAS


#### Documentation
In preparation.

You will find chapter 1 of the `book` as notebook (sections) at
[nb/ug](https://github.com/nilqed/fricas_input). 


#### Notebooks 
A lot of notebooks (converted from the .input files) can be found at
https://github.com/nilqed/fricas_input

Have a look into the folder nb/fricas_input/nbconvert.ipynb/ where one
can render a notebook by clicking.


#### Update 
17-JUN-2016 : pzmq -- https://github.com/orivej/pzmq.git

Change in the size of the message structure, zmq_msg_t, in 0MQ version 4.1.x 
to 64 bytes from a size of 32 bytes in version 4.0.x.

---
Development: [iSPAD](https://bitbucket.org/kfp/ispad) 

Features: [HTML export](http://kfp.bitbucket.org/tmp/version-0-9-2.html)