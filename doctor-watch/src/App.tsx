import React from 'react';
import Application from "./components/Application";

function App() {
    return (
        <>
            <Application context={{
                projectName: 'Doctor Watch',
                alternativeSite: 'Dentist Watch'
            }}></Application>
        </>
    );
}

export default App;
