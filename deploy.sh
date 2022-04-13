#!/bin/bash
set -e # Exit with nonzero exit code if anything fails

# Set up some git information.
REPO=`git config remote.origin.url`
SSH_REPO=${REPO/https:\/\/github.com\//git@github.com:}
SHA=`git rev-parse --verify HEAD`

SOURCE_BRANCH="master"
TARGET_BRANCH="gh-pages"

function doCompile {
    make
    make pdf
}

# Pull requests and commits to other branches shouldn't try to deploy, just build to verify
#if [ "$TRAVIS_PULL_REQUEST" != "false" -o "$TRAVIS_BRANCH" != "$SOURCE_BRANCH" ]; then
#    echo "Skipping deploy; not the right kind of build."
#    exit 0
#fi

# Clone the existing gh-pages for this repo into a temporary folder $CHECKOUT.
CHECKOUT=`mktemp -d`
git clone $REPO $CHECKOUT
git -C $CHECKOUT config user.name "GitHub Actions"
git -C $CHECKOUT config user.email "$COMMIT_AUTHOR_EMAIL"
# Create a new empty branch if gh-pages doesn't exist yet (should only happen on first deploy).
git -C $CHECKOUT checkout $TARGET_BRANCH || git -C $CHECKOUT checkout --orphan $TARGET_BRANCH

# Replace existing contents of checkout with the results of a fresh compile.
rm -rf $CHECKOUT/* || exit 0
doCompile
for x in book code code_ERRORexamples code_ObsEquiv images
do
    cp -r $x $CHECKOUT
done
mkdir -p $CHECKOUT/tex
cp tex/tamarin-manual.pdf $CHECKOUT/tex/tamarin-manual.pdf
cp index.html $CHECKOUT/index.html

# If there are no changes to the compiled book (e.g. this is a README update) then just bail.
if [[ -z `git -C $CHECKOUT status --porcelain` ]]; then
    echo "No changes to the output on this push; exiting."
    exit 0
fi

# Commit the "changes", i.e. the new version. The delta will show diffs between new and old versions.
git -C $CHECKOUT add \*
git -C $CHECKOUT commit -m "Deploy to GitHub Pages: ${SHA}"

# Get the deploy key by using Githubs's stored variables to decrypt deploy_key.enc.
openssl enc -nosalt -aes-256-cbc -d -in deploy_key.enc -out deploy_key -base64 -K $ENCRYPTED_KEY -iv $ENCRYPTED_IV
chmod 600 deploy_key
eval `ssh-agent -s`
ssh-add deploy_key

# Now that we're all set up, we can push.
git -C $CHECKOUT push $SSH_REPO $TARGET_BRANCH

# Clean up after ourselves.
rm -rf $CHECKOUT
