git clone git@github.com:honours-theses/Chew-MCS.git MCS-Proj

rm -rf MCS-Proj/stabilizer/barebone/
cp -r ../barebone/ MCS-Proj/stabilizer/barebone/

rm -rf MCS-Proj/stabilizer/mathcomp/
cp -r ../mathcomp/ MCS-Proj/stabilizer/mathcomp/

cd MCS-Proj
git add .
git status
git commit -m "sync code from 'git@github.com:ExcitedSpider/SQIR.git'"
git push

cd ..
rm -rf MCS-Proj
