# echo ""
# echo "-----------------------------------------"
# echo "Welcome to CrossPyInstall (a python pyinstall environment"
# echo "-----------------------------------------"
# echo ""
# echo "- User $(whoami) [$(id -u $USER)] | Group: $(id -g -n) [$(id -g)]"
# echo "- HOME:                ${HOME}"
# echo "- WORKDIR:             ${WORKDIR}"

. $HOME/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true

export DEEPSEC_DIR_IMAGE="VAR_DEEPSEC_DIR_IMAGE"
export PROVERIF_DIR_IMAGE="VAR_PROVERIF_DIR_IMAGE"
export GSVERIF_DIR_IMAGE="VAR_GSVERIF_DIR_IMAGE"

export PATH=$PATH:~/.local/bin:$DEEPSEC_DIR_IMAGE:$PROVERIF_DIR_IMAGE:$GSVERIF_DIR_IMAGE
export DEEPSEC_DIR=$DEEPSEC_DIR_IMAGE/deepsec

# if [ -f ${VIRTUALENV_PATH_EXTERNAL}/bin/activate ]; then
#     source ${VIRTUALENV_PATH_EXTERNAL}/bin/activate
#     echo "- Python Environment:  ${VIRTUALENV_PATH_EXTERNAL}"
# else
#     source ${VIRTUALENV_PATH}/bin/activate
#     echo "- Python Environment:  ${VIRTUALENV_PATH} (Using Default '${VIRTUALENV_PATH_EXTERNAL}' is empty)"
# fi

echo ""
