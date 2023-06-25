cd common-watch &&
npm run build
npm version patch
npm publish --access=public
cd ..
cd dentist-watch &&
ncu -u common-watch
npm install
cd ..
cd doctor-watch &&
ncu -u common-watch
npm install
