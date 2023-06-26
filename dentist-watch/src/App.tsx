import React from 'react';
import {Application} from "common-watch";

function App() {
    return (
        <>
            <Application context={{
                projectName: 'Dentist Watch',
                alternativeSite: 'Doctor Watch'
            }}></Application>
        </>
    );
}

export default App;
