cd common-watch
npm version patch
npm publish
cd ..
cd dentist-watch
ncu -u common-watch
npm install
cd ..
cd doctor-watch
ncu -u common-watch
npm install
