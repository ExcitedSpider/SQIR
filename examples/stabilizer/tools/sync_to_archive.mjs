#!/usr/bin/env zx
const fs = require('fs');
$.verbose = true;

cd(__dirname)

const rmDisclamer = `This folder is synced from https://github.com/ExcitedSpider/SQIR/tree/main/examples/stabilizer. And it only contains minimal files for simplicity. If you are going to run it, You should go to the original repo and following the instruction. 
`

async function prepareReadme() {
  const readmePath = "MCS-Proj/stabilizer/readme.md"
  await $`rm ${readmePath}`
  await $`echo "${rmDisclamer}" >> ${readmePath}`
  await $`cat ../readme.md >> ${readmePath}`
}

try {
  await $`git clone git@github.com:honours-theses/Chew-MCS.git MCS-Proj`

  await Promise.all(
    [
      $`rm -rf MCS-Proj/stabilizer/barebone/ && cp -r ../barebone/ MCS-Proj/stabilizer/barebone/`,
      $`rm -rf MCS-Proj/stabilizer/mathcomp/ && cp -r ../mathcomp/ MCS-Proj/stabilizer/mathcomp/`,
      prepareReadme()
      // $`rm MCS-Proj/stabilizer/readme.md && cp ../readme.md MCS-Proj/stabilizer/`
    ],
  )

  cd("MCS-Proj")
  
  await $`git add .`
  await $`git status`
  await $`git commit -m "sync code from 'git@github.com:ExcitedSpider/SQIR.git'"`
  await $`git push`
  
  
} finally {
  cd(__dirname)
  fs.existsSync("MCS-Proj") && await $`rm -rf MCS-Proj`
}

