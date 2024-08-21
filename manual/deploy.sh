#!/bin/bash
set -e # Exit with nonzero exit code if anything fails

# Set up some git information.
REPO="git@github.com:tamarin-prover/manual.git" #OLD for same repo: `git config remote.${1:-origin}.url`
SSH_REPO=${REPO/https:\/\/github.com\//git@github.com:}
SHA=`git rev-parse --verify HEAD`
BRANCH=`git rev-parse --abbrev-ref HEAD`

MASTER_BRANCH="master"
DEVELOP_BRANCH="develop"
TARGET_BRANCH="gh-pages"

function doCompile {
    make
    make pdf
}

if [ "$BRANCH" != "$MASTER_BRANCH" && "$BRANCH" != "$DEVELOP_BRANCH" ]; then
    echo "Please use this script on branch '$MASTER_BRANCH' or '$DEVELOP_BRANCH' only. You seem to be on '$BRANCH'."
    exit 0
fi

# Clone the existing gh-pages for this repo into a temporary folder $CHECKOUT.
CHECKOUT=`mktemp -d`
git clone $REPO $CHECKOUT
git -C $CHECKOUT config user.name "GitHub Actions"
git -C $CHECKOUT config user.email "$COMMIT_AUTHOR_EMAIL"
# Create a new empty branch if gh-pages doesn't exist yet (should only happen on first deploy).
git -C $CHECKOUT checkout $TARGET_BRANCH || git -C $CHECKOUT checkout --orphan $TARGET_BRANCH

# Replace existing contents of checkout with the results of a fresh compile.
rm -rf $CHECKOUT/$BRANCH || exit 0
mkdir -p $CHECKOUT/$BRANCH/tex
cd manual
doCompile
for x in book code code_ERRORexamples code_ObsEquiv images
do
    cp -r $x $CHECKOUT/$BRANCH
done
cp tex/tamarin-manual.pdf $CHECKOUT/$BRANCH/tex/tamarin-manual.pdf
# put index.html to root directory
cp index.html $CHECKOUT/index.html

# If there are no changes to the compiled book (e.g. this is a README update) then just bail.
if [[ -z `git -C $CHECKOUT status --porcelain` ]]; then
    echo "No changes to the output on this push; exiting."
    exit 0
fi

# Commit the "changes", i.e. the new version. The delta will show diffs between new and old versions.
git -C $CHECKOUT add \*
git -C $CHECKOUT commit -m "Deploy to GitHub Pages on ${BRANCH}: ${SHA}"

# Get the deploy key by using Githubs's stored variables to decrypt deploy_key.enc.
openssl enc -nosalt -aes-256-cbc -d -in deploy_key.enc -out deploy_key -base64 -K $ENCRYPTED_KEY -iv $ENCRYPTED_IV
chmod 600 deploy_key
eval `ssh-agent -s`
ssh-add deploy_key

# Now that we're all set up, we can push.
git -C $CHECKOUT push $SSH_REPO $TARGET_BRANCH

# Clean up after ourselves.
rm -rf $CHECKOUT
